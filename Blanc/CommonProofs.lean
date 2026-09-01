-- CommonProofs.lean : proof layers downstream of Blanc's tactic machinery.

import Blanc.Tactics
import Blanc.ExecutionSettlement

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

-- Splitting a body's line at any point and prepending the pieces in order is
-- the same as prepending the whole line. Every module that decomposes a
-- compiled body into named line segments needs this, so it is stated once here
-- rather than re-derived beside each decomposition.
lemma prepend_append (left right : Line) (tail : Func) :
    (left ++ right) +++ tail = left +++ (right +++ tail) := by
  induction left with
  | nil => rfl
  | cons head left ih => simp [prepend, ih]

-- The statement is unchanged by the `.rev` normalization (`Func.rev` in
-- `Blanc/CommonCore.lean`); only the walk is. `Func.rev` is now two `PUSH0`s
-- ahead of the failing `.rev`, so the run is peeled through two `next` binds
-- before the `Linst.Run` contradiction that has always closed this.
lemma not_run_rev {c e s r} : ¬ Func.Run c e s Func.rev r := by
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

lemma of_run_branch_rev {c e s r} {p : Func} (h : Func.Run c e s (.rev <?> p) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r := by
  rcases of_run_branch h with ⟨s', h_pb, h_run⟩ | ⟨w, s', s'', h_ne, h_pb, h_b, h_run⟩
  · exact ⟨s', h_pb, h_run⟩
  · exfalso; exact not_run_rev h_run

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
contracts whose selector miss is a direct `Func.rev`, rather than an indexed
fallback call.  This is the exact analogue of `dispatchWith_inv`: comparison
lines preserve the carried entry predicate, a successful leaf reaches its
body, and the miss arm is impossible because `Func.rev` has no successful
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
      · exact absurd h_run' not_run_rev
      · exact htt' ⟨w, p⟩ rfl
          (h0 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'

-- Tree membership implies list membership. `dispatchWith_inv` puts `wf ∈ t` in
-- hypothesis position, so a contract built with `ofSorted` needs to discharge
-- its per-leaf obligation over its own *list* rather than over the balanced
-- tree shape. Only the forward direction is needed.
--
-- The fuel bound is the lemma's content, not decoration: `build`'s two
-- degenerate rows (`| _, [] => leaf 0 .rev` and `| 0, (x :: _ :: _) =>
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
        simp [h]
      · simp only [List.length_cons] at h_len; omega
  | succ n ih =>
    intro xs wp h_ne h_len h_mem
    rcases xs with _ | ⟨⟨w, p⟩, xs'⟩
    · exact absurd rfl h_ne
    · rcases xs' with _ | ⟨y, ys⟩
      · have h : wp = (w, p) := h_mem
        simp [h]
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

lemma State.setBal_getCode (st : State) (adr a : Adr) (val : B256) :
  (st.setBal adr val).getCode a = st.getCode a := by
  dsimp [State.setBal, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      dsimp [Acct.withBal]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma State.addBal_getCode (st : State) (adr a : Adr) (val : B256) :
  (st.addBal adr val).getCode a = st.getCode a := by
  dsimp [State.addBal]
  exact State.setBal_getCode st adr a (st.bal adr + val)

lemma State.subBal_getCode {st st' : State} {adr a : Adr} {val : B256} (h : st.subBal adr val = some st') :
  st'.getCode a = st.getCode a := by
  dsimp [State.subBal] at h
  split at h
  · contradiction
  · injection h with h2
    subst h2
    exact State.setBal_getCode st adr a (st.bal adr - val)

lemma Benv.addBal_getCode (benv : Benv) (adr a : Adr) (val : B256) :
  (benv.addBal adr val).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.addBal, Benv.withState]
  exact State.addBal_getCode benv.state adr a val

lemma Benv.subBal_getCode {benv benv' : Benv} {adr a : Adr} {val : B256} (h : benv.subBal adr val = some benv') :
  benv'.state.getCode a = benv.state.getCode a := by
  dsimp [Benv.subBal, Option.bind] at h
  split at h
  · contradiction
  · rename_i st' h_sub
    injection h with h2
    subst h2
    dsimp [Benv.withState]
    exact State.subBal_getCode h_sub

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
  | error err => simp [hc] at h
  | ok out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2

lemma liftMach_worldEq_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : EvmError × Devm} (h : liftMach core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2
  | ok out => simp [hc] at h

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

lemma Devm.WorldEq.getCode {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.1]

lemma Devm.WorldEq.getBal {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.1]

lemma addAccessedAddress_getCode {devm : Devm} {adr a : Adr} :
    (addAccessedAddress devm adr).getCode a = devm.getCode a := by
  exact (addAccessedAddress_worldEq devm adr).getCode a |>.symm

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

lemma Devm.memExtends_getCode {devm : Devm} {ranges : List (ℕ × ℕ)} {a : Adr} :
    (devm.memExtends ranges).getCode a = devm.getCode a := by
  exact (liftMachPure_worldEq (Mach.memExtends · ranges) devm).getCode a |>.symm

lemma Devm.incrNonce_getCode {devm : Devm} {adr a : Adr} : (devm.incrNonce adr).getCode a = devm.getCode a := by
  dsimp [Devm.incrNonce, Devm.withState, Devm.setWorld, Devm.world, Devm.state,
    Devm.getCode, Devm.getAcct, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma addCreatedAccount_getCode {benv : Benv} {adr a : Adr} : (addCreatedAccount benv adr).state.getCode a = benv.state.getCode a := by
  rfl

lemma Benv.setStor_getCode {benv : Benv} {adr a : Adr} {stor : Stor} : (benv.setStor adr stor).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.setStor, Benv.state, State.setStor, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma Benv.incrNonce_getCode {benv : Benv} {adr a : Adr} : (benv.incrNonce adr).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.incrNonce, Benv.state, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma ExecuteCode.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ExecuteCode msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth := by
  rw [(ExecuteCode.some_inv run).1]; rfl

lemma ProcessMessage.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ProcessMessage msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth :=
  RunFrame.depth_eq run

lemma ProcessCreateMessage.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ProcessCreateMessage msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth :=
  RunFrame.depth_eq run

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

lemma chargeGas_getCode_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma Devm.push_getCode_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToAdr_getCode_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

@[simp] lemma Except.bind_error {α β ε} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
@[simp] lemma Except.bind_ok {α β ε} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

lemma chargeGas_getBal_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (chargeGas_worldEq_of_ok h).getBal a |>.symm

lemma Devm.push_getBal_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getBal a |>.symm

lemma Devm.popToAdr_getBal_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getBal a |>.symm

lemma Devm.popToNat_getBal_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (Devm.popToNat_worldEq_of_ok h).getBal a |>.symm

def Devm.getStor (devm : Devm) (adr : Adr) : Stor :=
  (devm.getAcct adr).stor

lemma Devm.withRefundCounter_getStor (devm : Devm) (refundCounter : Int) :
    Devm.getStor (devm.withRefundCounter refundCounter) = Devm.getStor devm := by
  rfl

lemma Devm.addLog_getStor (devm : Devm) (log : Log) :
    Devm.getStor (devm.addLog log) = Devm.getStor devm := by
  rfl

lemma Devm.WorldEq.getStor {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.1]

lemma Devm.Burn.getStor {s s' : Devm} (h : Devm.Burn s s') (a : Adr) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp [Devm.getStor, Devm.getAcct]; rw [h.state]

lemma Devm.PopBurn.getStor {xs} {s s' : Devm} (h : Devm.PopBurn xs s s') (a : Adr) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp [Devm.getStor, Devm.getAcct]; rw [h.state]

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

lemma setStorVal_getStor_ne {devm : Devm} {adr a : Adr}
    {key val : B256} (h : adr ≠ a) :
    Devm.getStor (devm.setStorVal adr key val) a = Devm.getStor devm a := by
  simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
    Devm.setWorld, State.setStorVal]
  simp only [Devm.state, State.get_set_ne _ h]

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

/-- A `SilentIn` body preserves its observation in a fixed function context
closed under permitted tail calls.  Recursion is on the successful run, so a
closed set of mutually recursive slots needs no fuel premise. -/
theorem Func.observe_eq_of_run_silentIn
    {Observation : Type} {observe : Devm → Observation}
    {P : Nat → Prop} {fs : List Func}
    [PopBurn.Inv observe] [Burn.Inv observe]
    (hclosed : ∀ k g, P k → fs[k]? = some g → Func.SilentIn observe P g)
    {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run fs sevm s f r)
    (silent : Func.SilentIn observe P f) :
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

/-! ## Fieldwise `Devm.Rel` infrastructure -/

/-- Functional compatibility form of reflexivity, avoiding the deprecated root alias. -/
abbrev ReflexiveRel {α : Sort*} (r : α → α → Prop) : Prop := ∀ x, r x x

/-- Functional compatibility form of transitivity, avoiding the deprecated root alias. -/
abbrev TransitiveRel {α : Sort*} (r : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, r x y → r y z → r x z

def Devm.Rels.Refl (r : Devm.Rels) : Prop :=
  ReflexiveRel r.stack ∧ ReflexiveRel r.memory ∧ ReflexiveRel r.gasLeft ∧
  ReflexiveRel r.logs ∧ ReflexiveRel r.refundCounter ∧ ReflexiveRel r.output ∧
  ReflexiveRel r.accountsToDelete ∧ ReflexiveRel r.returnData ∧ ReflexiveRel r.error ∧
  ReflexiveRel r.accessedAddresses ∧ ReflexiveRel r.accessedStorageKeys ∧
  ReflexiveRel r.state ∧ ReflexiveRel r.createdAccounts ∧
  ReflexiveRel r.transientStorage

def Devm.Rels.Trans (r : Devm.Rels) : Prop :=
  TransitiveRel r.stack ∧ TransitiveRel r.memory ∧ TransitiveRel r.gasLeft ∧
  TransitiveRel r.logs ∧ TransitiveRel r.refundCounter ∧ TransitiveRel r.output ∧
  TransitiveRel r.accountsToDelete ∧ TransitiveRel r.returnData ∧ TransitiveRel r.error ∧
  TransitiveRel r.accessedAddresses ∧ TransitiveRel r.accessedStorageKeys ∧
  TransitiveRel r.state ∧ TransitiveRel r.createdAccounts ∧
  TransitiveRel r.transientStorage

lemma Devm.rel_refl {r : Devm.Rels} (hr : Devm.Rels.Refl r) :
    ReflexiveRel (Devm.Rel r) := by
  intro d
  rcases hr with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  constructor
  · exact h1 _
  · exact h2 _
  · exact h3 _
  · exact h4 _
  · exact h5 _
  · exact h6 _
  · exact h7 _
  · exact h8 _
  · exact h9 _
  · exact h10 _
  · exact h11 _
  · exact h12 _
  · exact h13 _
  · exact h14 _

lemma Devm.rel_trans {r : Devm.Rels} (hr : Devm.Rels.Trans r) :
    TransitiveRel (Devm.Rel r) := by
  intro a b c hab hbc
  constructor
  · exact hr.1 hab.stack hbc.stack
  · exact hr.2.1 hab.memory hbc.memory
  · exact hr.2.2.1 hab.gasLeft hbc.gasLeft
  · exact hr.2.2.2.1 hab.logs hbc.logs
  · exact hr.2.2.2.2.1 hab.refundCounter hbc.refundCounter
  · exact hr.2.2.2.2.2.1 hab.output hbc.output
  · exact hr.2.2.2.2.2.2.1 hab.accountsToDelete hbc.accountsToDelete
  · exact hr.2.2.2.2.2.2.2.1 hab.returnData hbc.returnData
  · exact hr.2.2.2.2.2.2.2.2.1 hab.error hbc.error
  · exact hr.2.2.2.2.2.2.2.2.2.1 hab.accessedAddresses hbc.accessedAddresses
  · exact hr.2.2.2.2.2.2.2.2.2.2.1 hab.accessedStorageKeys hbc.accessedStorageKeys
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.1 hab.state hbc.state
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.1 hab.createdAccounts hbc.createdAccounts
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2 hab.transientStorage hbc.transientStorage

/-! ## Outcome-aware effects for the EVM semantic layers -/

namespace Outcome

/-- Outcome-aware lifting of a state relation across both `Except` branches. -/
def Rel {σ ε α : Type}
    (errState : ε → σ) (okState : α → σ)
    (R : σ → σ → Prop) (pre : σ) : Except ε α → Prop
  | .error err => R pre (errState err)
  | .ok value => R pre (okState value)

/-
This is the generic weakening rule for both success and error outcomes.
-/
lemma Rel.mono {σ ε α : Type}
    {errState : ε → σ} {okState : α → σ} {R S : σ → σ → Prop}
    {pre : σ} {out : Except ε α}
    (hrefine : ∀ ⦃s t⦄, R s t → S s t)
    (h : Rel errState okState R pre out) :
    Rel errState okState S pre out := by
  cases out <;> exact hrefine h

end Outcome

/-- Canonical outcome-aware preservation statement for dynamic EVM execution. -/
def Execution.Rel (R : Devm → Devm → Prop) (pre : Devm) (out : Execution) : Prop :=
  Outcome.Rel Prod.snd id R pre out

lemma outcomeRel_toExecution {R : Devm → Devm → Prop} {pre : Devm}
    {out : Except (EvmError × Devm) (Unit × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd R pre out) :
    Execution.Rel R pre (Footprint.toExecution out) := by
  cases out <;> exact h

-- The full-frame infrastructure and master regular-instruction theorem are
-- declared here so that the legacy observation lemmas below can be stated as
-- projections of them.

-- Paired projection of the two deletion-relevant sets
def Devm.delSets (d : Devm) : AdrSet × AdrSet :=
  (d.accountsToDelete, d.createdAccounts)

/-! ## Full-frame relations for instruction preservation -/

/-- A Mach-only step may change exactly the three `Mach` fields. -/
def Devm.Rels.machFrame : Devm.Rels :=
  { Devm.Rels.eq with
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True }

/-- A regular instruction may change every field except the world and the two
    deletion-relevant sets. -/
def Devm.Rels.instructionFrame : Devm.Rels :=
  {
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    logs := fun _ _ => True
    refundCounter := fun _ _ => True
    output := fun _ _ => True
    accountsToDelete := _root_.Eq
    returnData := fun _ _ => True
    error := fun _ _ => True
    accessedAddresses := fun _ _ => True
    accessedStorageKeys := fun _ _ => True
    state := _root_.Eq
    createdAccounts := _root_.Eq
    transientStorage := _root_.Eq }

abbrev Devm.MachFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.machFrame

abbrev Devm.InstructionFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.instructionFrame

/-- The part of `Meta` that an instruction-frame lift must preserve. -/
def Meta.InstructionFrame (a b : Meta) : Prop :=
  a.accountsToDelete = b.accountsToDelete ∧
    a.createdAccounts = b.createdAccounts

lemma Devm.Rels.instructionFrame_refl :
    Devm.Rels.Refl Devm.Rels.instructionFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.instructionFrame, ReflexiveRel]

lemma Devm.Rels.instructionFrame_trans :
    Devm.Rels.Trans Devm.Rels.instructionFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.instructionFrame, TransitiveRel]

lemma Devm.instructionFrame_refl : ReflexiveRel Devm.InstructionFrame :=
  Devm.rel_refl Devm.Rels.instructionFrame_refl

lemma Devm.instructionFrame_trans : TransitiveRel Devm.InstructionFrame :=
  Devm.rel_trans Devm.Rels.instructionFrame_trans

lemma Devm.machFrame_refines_instructionFrame :
    ∀ ⦃d d'⦄, Devm.MachFrame d d' → Devm.InstructionFrame d d' := by
  intro d d' h
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := h.accountsToDelete
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := h.state
    createdAccounts := h.createdAccounts
    transientStorage := h.transientStorage }

lemma Devm.InstructionFrame.getBal {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.getStor {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.getCode {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.delSets {d d' : Devm}
    (h : Devm.InstructionFrame d d') :
    Devm.delSets d = Devm.delSets d' :=
  Prod.ext h.accountsToDelete h.createdAccounts

lemma Devm.machFrame_setMach (d : Devm) (mach : Mach) :
    Devm.MachFrame d (d.setMach mach) := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := rfl
    refundCounter := rfl
    output := rfl
    accountsToDelete := rfl
    returnData := rfl
    error := rfl
    accessedAddresses := rfl
    accessedStorageKeys := rfl
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl }

lemma Devm.instructionFrame_setMachMeta (d : Devm) (view : Mach × Meta)
    (h : Meta.InstructionFrame d.meta view.2) :
    Devm.InstructionFrame d
      { d with mach := view.1, «meta» := view.2 } := by
  rcases h with ⟨hdel, hcreated⟩
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := hcreated
    transientStorage := rfl }

/-! ### Full-frame lift rules -/

lemma liftMach_machFrame (core : Mach → Footprint.Outcome Mach α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (liftMach core d) := by
  unfold liftMach Footprint.liftOutcome
  cases core d.mach <;> exact Devm.machFrame_setMach d _

lemma liftMachPure_machFrame (core : Mach → Mach) (d : Devm) :
    Devm.MachFrame d (liftMachPure core d) := by
  exact Devm.machFrame_setMach d _

lemma liftMachExecution_machFrame
    (core : Mach → Footprint.Outcome Mach Unit) (d : Devm) :
    Execution.Rel Devm.MachFrame d (liftMachExecution core d) := by
  unfold liftMachExecution
  exact outcomeRel_toExecution (liftMach_machFrame core d)

lemma liftMachMeta_instructionFrame
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α) (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.mach d.meta)) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d
      (liftMachMeta core d) := by
  cases h : core d.mach d.meta with
  | error e =>
      rw [h] at hcore
      simpa only [liftMachMeta, Footprint.liftOutcome, h, Outcome.Rel] using
        Devm.instructionFrame_setMachMeta d e.2 hcore
  | ok x =>
      rw [h] at hcore
      simpa only [liftMachMeta, Footprint.liftOutcome, h, Outcome.Rel] using
        Devm.instructionFrame_setMachMeta d x.2 hcore

lemma liftMachMetaPure_instructionFrame
    (core : Mach → Meta → Mach × Meta) (d : Devm)
    (hcore : Meta.InstructionFrame d.meta (core d.mach d.meta).2) :
    Devm.InstructionFrame d (liftMachMetaPure core d) := by
  exact Devm.instructionFrame_setMachMeta d _ hcore

lemma liftMachMetaExecution_instructionFrame
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit) (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.mach d.meta)) :
    Execution.Rel Devm.InstructionFrame d (liftMachMetaExecution core d) := by
  unfold liftMachMetaExecution
  exact outcomeRel_toExecution (liftMachMeta_instructionFrame core d hcore)

lemma liftMachMetaWorldExecution_instructionFrame
    (core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.world d.mach d.meta)) :
    Execution.Rel Devm.InstructionFrame d
      (liftMachMetaWorldExecution core d) := by
  exact liftMachMetaExecution_instructionFrame (core d.world) d hcore

/-! ### Full-frame primitive facts -/

lemma Devm.pop_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.pop d) := by
  exact liftMach_machFrame Mach.pop d

lemma Devm.pop_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.pop d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.pop_machFrame d)

lemma Devm.push_machFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.MachFrame d (Devm.push x d) := by
  exact liftMachExecution_machFrame (Mach.push x) d

lemma Devm.push_instructionFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (Devm.push x d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.push_machFrame x d)

lemma pushItem_machFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (pushItem x cost d) := by
  exact liftMachExecution_machFrame (Mach.pushItem x cost) d

lemma pushItem_instructionFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (pushItem x cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (pushItem_machFrame x cost d)

lemma chargeGas_machFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (chargeGas cost d) := by
  exact liftMachExecution_machFrame (Mach.chargeGas cost) d

lemma chargeGas_instructionFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (chargeGas cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (chargeGas_machFrame cost d)

lemma Devm.popToNat_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToNat d) := by
  exact liftMach_machFrame Mach.popToNat d

lemma Devm.popToNat_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToNat d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToNat_machFrame d)

lemma Devm.popToAdr_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToAdr d) := by
  exact liftMach_machFrame Mach.popToAdr d

lemma Devm.popToAdr_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToAdr d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToAdr_machFrame d)

lemma Devm.popN_machFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popN d n) := by
  exact liftMach_machFrame (Mach.popN · n) d

lemma Devm.popN_instructionFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popN d n) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popN_machFrame d n)

lemma applyUnary_machFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyUnary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyUnary f cost) d

lemma applyUnary_instructionFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyUnary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyUnary_machFrame f cost d)

lemma applyBinary_machFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyBinary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyBinary f cost) d

lemma applyBinary_instructionFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyBinary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyBinary_machFrame f cost d)

lemma applyTernary_machFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyTernary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyTernary f cost) d

lemma applyTernary_instructionFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyTernary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyTernary_machFrame f cost d)

lemma Devm.memWrite_machFrame (d : Devm) (idx : Nat) (val : Bytes) :
    Devm.MachFrame d (Devm.memWrite d idx val) := by
  exact liftMachPure_machFrame (Mach.memWrite · idx val) d

lemma Devm.memWrite_instructionFrame (d : Devm) (idx : Nat) (val : Bytes) :
    Devm.InstructionFrame d (Devm.memWrite d idx val) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memWrite_machFrame d idx val)

lemma Devm.memExtends_machFrame (d : Devm) (ranges : List (Nat × Nat)) :
    Devm.MachFrame d (Devm.memExtends d ranges) := by
  exact liftMachPure_machFrame (Mach.memExtends · ranges) d

lemma Devm.memExtends_instructionFrame (d : Devm)
    (ranges : List (Nat × Nat)) :
    Devm.InstructionFrame d (Devm.memExtends d ranges) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memExtends_machFrame d ranges)

lemma addAccessedAddress_instructionFrame (d : Devm) (a : Adr) :
    Devm.InstructionFrame d (addAccessedAddress d a) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

/-- Access-delegation resolves an EOA delegation without touching the world or
    the deletion sets, so it stays inside the instruction frame. -/
lemma accessDelegation_instructionFrame (d : Devm) (adr : Adr) :
    Devm.InstructionFrame d (accessDelegation d adr).2.2.2.2 := by
  rw [accessDelegation]
  cases getDelegatedCodeAddress (d.state.getCode adr)
  · exact Devm.instructionFrame_refl d
  · exact addAccessedAddress_instructionFrame d _

lemma addAccessedStorageKey_instructionFrame
    (d : Devm) (a : Adr) (k : B256) :
    Devm.InstructionFrame d (addAccessedStorageKey d a k) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.addLog_instructionFrame (d : Devm) (log : Log) :
    Devm.InstructionFrame d (Devm.addLog d log) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.memRead_instructionFrame (d : Devm) (index size : Nat) :
    Devm.InstructionFrame d (Devm.memRead d index size).2 := by
  unfold Devm.memRead
  split
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := rfl
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl }

lemma Rinst.balanceCore_meta_instructionFrame
    (world : World) (mach : Mach) (view : Meta) :
    Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame view (Rinst.balanceCore world mach view) := by
  cases hpop : mach.pop with
  | error e =>
      simp only [Rinst.balanceCore, hpop]
      exact ⟨rfl, rfl⟩
  | ok out =>
      rcases out with ⟨x, mach'⟩
      simp only [Rinst.balanceCore, hpop]
      by_cases hw : x.toAdr ∈ view.accessedAddresses
      · simp only [hw, if_pos]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩
      · simp only [hw, if_false]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩

lemma Rinst.balanceCore_instructionFrame (d : Devm) :
    Execution.Rel Devm.InstructionFrame d
      (liftMachMetaWorldExecution Rinst.balanceCore d) := by
  exact liftMachMetaWorldExecution_instructionFrame Rinst.balanceCore d
    (Rinst.balanceCore_meta_instructionFrame d.world d.mach d.meta)

/-! ### Bind composition for frame relations -/

lemma Outcome.Rel.bindExecution
    {R : Devm → Devm → Prop} (htrans : TransitiveRel R)
    {pre : Devm} {out : Except (EvmError × Devm) (α × Devm)}
    {next : α → Devm → Execution}
    (hout : Outcome.Rel Prod.snd Prod.snd R pre out)
    (hnext : ∀ x d, Execution.Rel R d (next x d)) :
    Execution.Rel R pre (out >>= fun x => next x.1 x.2) := by
  cases out with
  | error e => exact hout
  | ok x =>
      cases hn : next x.1 x.2 with
      | error e =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, Execution.Rel, Outcome.Rel] using htrans hout h
      | ok d =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq, Execution.Rel, Outcome.Rel] using htrans hout h

lemma Execution.Rel.bind
    {R : Devm → Devm → Prop} (htrans : TransitiveRel R)
    {pre : Devm} {out : Execution} {next : Devm → Execution}
    (hout : Execution.Rel R pre out)
    (hnext : ∀ d, Execution.Rel R d (next d)) :
    Execution.Rel R pre (out >>= next) := by
  cases out with
  | error e => exact hout
  | ok d =>
      cases hn : next d with
      | error e =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, Execution.Rel, Outcome.Rel] using htrans hout h
      | ok d' =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq, Execution.Rel, Outcome.Rel] using htrans hout h

/-! ### Step 3 calibration cases -/

lemma Rinst.balance_runCore_instructionFrame
    (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame devm
      (Rinst.runCore pc devm sevm .balance) := by
  simpa only [Rinst.runCore] using Rinst.balanceCore_instructionFrame devm

lemma Rinst.blobhash_runCore_instructionFrame
    (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame devm
      (Rinst.runCore pc devm sevm .blobhash) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame devm) (next := fun x d =>
      chargeGas gHashopcode d >>=
        Devm.push (sevm.tenvStat.blobVersionedHashes.getD x.toNat 0)) ?_
  intro x d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gHashopcode d)
  exact Devm.push_instructionFrame _

/-! ## Master regular-instruction frame theorem -/

/-- Equality of the balance/code observations of two world states.  Storage is
    deliberately absent: it is the component written by `SSTORE`. -/
def State.BalCodeEq (a b : Jaune.State) : Prop :=
  (fun adr => ((a.get adr).bal, (a.get adr).code)) =
    fun adr => ((b.get adr).bal, (b.get adr).code)

/-- Canonical precise effect of the persistent-storage writer: balances and
code are unchanged at every address. -/
lemma State.setStorVal_balCodeEq (st : Jaune.State)
    (adr : Adr) (key value : B256) :
    State.BalCodeEq st (st.setStorVal adr key value) := by
  unfold State.BalCodeEq State.setStorVal State.get State.set
  funext adr'
  dsimp
  split_ifs with h_if
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_erase]
      simp
      constructor
      · simpa only using congrArg Acct.bal h_if
      · simpa only using congrArg Acct.code h_if
    · rw [Std.TreeMap.getD_erase]
      simp [h_cmp]
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h_cmp]

/-- `SSTORE` may change storage in `state`, but preserves balances, code, and
    the other world/frame fields. -/
def Devm.Rels.stateWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with state := State.BalCodeEq }

/-- `TSTORE` may change `transientStorage`, but preserves the other
    world/frame fields. -/
def Devm.Rels.transientWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with transientStorage := fun _ _ => True }

abbrev Devm.StateWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.stateWriteFrame

abbrev Devm.TransientWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.transientWriteFrame

lemma Devm.Rels.stateWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.stateWriteFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.stateWriteFrame,
    Devm.Rels.instructionFrame, State.BalCodeEq, ReflexiveRel]

lemma Devm.Rels.stateWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.stateWriteFrame := by
  simp_all [Devm.Rels.Trans, Devm.Rels.stateWriteFrame,
    Devm.Rels.instructionFrame, State.BalCodeEq, TransitiveRel]

lemma Devm.Rels.transientWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.transientWriteFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.transientWriteFrame,
    Devm.Rels.instructionFrame, ReflexiveRel]

lemma Devm.Rels.transientWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.transientWriteFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.transientWriteFrame,
    Devm.Rels.instructionFrame, TransitiveRel]

lemma Devm.stateWriteFrame_refl : ReflexiveRel Devm.StateWriteFrame :=
  Devm.rel_refl Devm.Rels.stateWriteFrame_refl

lemma Devm.stateWriteFrame_trans : TransitiveRel Devm.StateWriteFrame :=
  Devm.rel_trans Devm.Rels.stateWriteFrame_trans

lemma Devm.transientWriteFrame_refl : ReflexiveRel Devm.TransientWriteFrame :=
  Devm.rel_refl Devm.Rels.transientWriteFrame_refl

lemma Devm.transientWriteFrame_trans : TransitiveRel Devm.TransientWriteFrame :=
  Devm.rel_trans Devm.Rels.transientWriteFrame_trans

lemma Devm.instructionFrame_refines_stateWriteFrame :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.StateWriteFrame d d' := by
  intro d d' h
  refine { h with state := ?_ }
  change State.BalCodeEq d.state d'.state
  rw [h.state]
  rfl

lemma Devm.instructionFrame_refines_transientWriteFrame :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.TransientWriteFrame d d' := by
  intro d d' h
  exact { h with transientStorage := trivial }

lemma Devm.instructionFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.InstructionFrame d d' := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := hstate
    createdAccounts := hcreated
    transientStorage := htransient }

lemma popChargePush_instructionFrame (pre : Devm)
    (cost : B256 → Devm → Nat) (value : B256 → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.pop
      let d ← chargeGas (cost x d) d
      d.push (value x d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun x d =>
      chargeGas (cost x d) d >>= fun d => Devm.push (value x d) d) ?_
  intro x d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x d) d)
  intro d'
  exact Devm.push_instructionFrame (value x d') d'

lemma Execution.Rel.trans_left {R : Devm → Devm → Prop}
    (htrans : TransitiveRel R) {a b : Devm} {out : Execution}
    (hab : R a b) (hout : Execution.Rel R b out) :
    Execution.Rel R a out := by
  cases out <;> exact htrans hab hout

lemma pop2ChargePush_instructionFrame (pre : Devm)
    (cost : B256 → B256 → Devm → Nat)
    (value : B256 → B256 → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.pop
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      d.push (value x y d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      d.push (value x y d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame d) (next := fun y d =>
      chargeGas (cost x y d) d >>= fun d => Devm.push (value x y d) d) ?_
  intro y d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y d) d)
  intro d'
  exact Devm.push_instructionFrame (value x y d') d'

lemma Rinst.exp_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .exp) := by
  simpa only [Rinst.runCore] using
    (pop2ChargePush_instructionFrame pre
      (fun _ exponent _ => gExp + gExpbyte * exponent.bytecount)
      (fun base exponent _ => B256.bexp base exponent))

lemma Rinst.calldataload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .calldataload) := by
  simpa only [Rinst.runCore] using
    (popChargePush_instructionFrame pre (fun _ _ => gVerylow)
      (fun start _ => Bytes.toB256 <| sevm.data.sliceD start.toNat 32 0))

lemma Rinst.blockhash_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .blockhash) := by
  simpa only [Rinst.runCore] using
    (popChargePush_instructionFrame pre (fun _ _ => gBlockhash)
      (fun blockNumberWord _ =>
        let blockNumber := blockNumberWord.toNat
        let maxBlockNumber := blockNumber + 256
        if sevm.benvStat.number ≤ blockNumber ∨
            maxBlockNumber < sevm.benvStat.number then 0
        else sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length -
            (sevm.benvStat.number - blockNumber)) 0))

lemma Rinst.gas_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .gas) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gBase pre)
  intro d
  exact Devm.push_instructionFrame d.gasLeft.toB256 d

/-- `CLZ` needs its own case because its body is fork-gated.

Where EIP-7939 is in force it is an ordinary unary operation; where it is not,
0x1E is an undefined byte and the instruction halts without touching the frame.
Both branches preserve the frame, so the statement is the same one every other
regular instruction satisfies and no fork hypothesis is needed. -/
lemma Rinst.clz_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .clz) := by
  simp only [Rinst.runCore]
  split
  · exact applyUnary_instructionFrame _ _ pre
  · exact Devm.instructionFrame_refl pre

lemma Rinst.tload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .tload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun key d =>
      pushItem (d.getTransVal sevm.currentTarget key) gasWarmAccess d) ?_
  intro key d
  exact pushItem_instructionFrame _ _ d

lemma popNat3ChargePure_instructionFrame (pre : Devm)
    (cost : Nat → Nat → Nat → Devm → Nat)
    (finish : Nat → Nat → Nat → Devm → Devm)
    (hfinish : ∀ x y z d, Devm.InstructionFrame d (finish x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun z d =>
      chargeGas (cost x y z d) d >>= fun d => .ok (finish x y z d)) ?_
  intro z d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y z d) d)
  intro d'
  exact hfinish x y z d'

lemma popNatPopChargePure_instructionFrame (pre : Devm)
    (cost : Nat → B256 → Devm → Nat)
    (finish : Nat → B256 → Devm → Devm)
    (hfinish : ∀ x y d, Devm.InstructionFrame d (finish x y d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      .ok (finish x y d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      .ok (finish x y d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame d) (next := fun y d =>
      chargeGas (cost x y d) d >>= fun d => .ok (finish x y d)) ?_
  intro y d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y d) d)
  intro d'
  exact hfinish x y d'

lemma Rinst.calldatacopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .calldatacopy) := by
  simpa only [Rinst.runCore] using
    (popNat3ChargePure_instructionFrame pre
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart dataStart size d =>
        d.memWrite memoryStart (sevm.data.sliceD dataStart size 0))
      (fun memoryStart dataStart size d =>
        Devm.memWrite_instructionFrame d memoryStart
          (sevm.data.sliceD dataStart size 0)))

lemma Rinst.codecopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .codecopy) := by
  simpa only [Rinst.runCore] using
    (popNat3ChargePure_instructionFrame pre
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart codeStart size d => d.memWrite memoryStart
        (sevm.code.sliceD codeStart size (Linst.toUInt8 .stop)))
      (fun memoryStart codeStart size d => Devm.memWrite_instructionFrame d
        memoryStart (sevm.code.sliceD codeStart size (Linst.toUInt8 .stop))))

lemma Rinst.mstore_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mstore) := by
  simpa only [Rinst.runCore] using
    (popNatPopChargePure_instructionFrame pre
      (fun start _ d => gVerylow + d.extCost [(start, 32)])
      (fun start value d => d.memWrite start value.toBytes)
      (fun start value d =>
        Devm.memWrite_instructionFrame d start value.toBytes))

lemma Rinst.mstore8_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mstore8) := by
  simpa only [Rinst.runCore] using
    (popNatPopChargePure_instructionFrame pre
      (fun start _ d => gVerylow + d.extCost [(start, 1)])
      (fun start value d => d.memWrite start [value.2.2.toUInt8])
      (fun start value d =>
        Devm.memWrite_instructionFrame d start [value.2.2.toUInt8]))

lemma Rinst.mload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun start d =>
      chargeGas (gVerylow + d.extCost [(start, 32)]) d >>= fun d =>
        Devm.push (Bytes.toB256 (d.memRead start 32).1) (d.memRead start 32).2) ?_
  intro start d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Execution.Rel.trans_left Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' start 32)
    (Devm.push_instructionFrame _ (d'.memRead start 32).2)

lemma Rinst.kec_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .kec) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun start d => do
      let ⟨size, d⟩ ← d.popToNat
      let d ← chargeGas
        (gKeccak256 + gasKeccak256Word * ceilDiv size 32 +
          d.extCost [(start, size)]) d
      let ⟨arg, d⟩ := d.memRead start size
      d.push arg.keccak) ?_
  intro start d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun size d =>
      chargeGas
        (gKeccak256 + gasKeccak256Word * ceilDiv size 32 +
          d.extCost [(start, size)]) d >>= fun d =>
        Devm.push (d.memRead start size).1.keccak (d.memRead start size).2) ?_
  intro size d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Execution.Rel.trans_left Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' start size)
    (Devm.push_instructionFrame _ (d'.memRead start size).2)

lemma Rinst.mcopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mcopy) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun destination d => do
      let ⟨source, d⟩ ← d.popToNat
      let ⟨length, d⟩ ← d.popToNat
      let d ← chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro destination d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun source d => do
      let ⟨length, d⟩ ← d.popToNat
      let d ← chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro source d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun length d =>
      chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d >>= fun d =>
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro length d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' source length)
    (Devm.memWrite_instructionFrame (d'.memRead source length).2 destination
      (d'.memRead source length).1)

lemma popAdrAccessChargePush_instructionFrame (pre : Devm)
    (value : Adr → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨a, d⟩ ← pre.popToAdr
      let d ← if a ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d a)
      d.push (value a d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToAdr_instructionFrame pre) (next := fun a d => do
      let d ← if a ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d a)
      d.push (value a d)) ?_
  intro a d
  by_cases h : a ∈ d.accessedAddresses
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame gasWarmAccess d)
    intro d'
    exact Devm.push_instructionFrame (value a d') d'
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedAddress_instructionFrame d a)
        (chargeGas_instructionFrame gasColdAccountAccess
          (addAccessedAddress d a)))
    intro d'
    exact Devm.push_instructionFrame (value a d') d'

lemma Rinst.extcodesize_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodesize) := by
  simpa only [Rinst.runCore] using
    (popAdrAccessChargePush_instructionFrame pre
      (fun a d => (d.getCode a).size.toB256))

lemma Rinst.extcodehash_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodehash) := by
  simpa only [Rinst.runCore] using
    (popAdrAccessChargePush_instructionFrame pre (fun a d =>
      let account := d.getAcct a
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code))

lemma Rinst.sload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .sload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun key d =>
      if (sevm.currentTarget, key) ∈ d.accessedStorageKeys then
        chargeGas gasWarmAccess d >>= fun d =>
          Devm.push (d.getStorVal sevm.currentTarget key) d
      else chargeGas gasColdSload
        (addAccessedStorageKey d sevm.currentTarget key) >>= fun d =>
          Devm.push (d.getStorVal sevm.currentTarget key) d) ?_
  intro key d
  by_cases h : (sevm.currentTarget, key) ∈ d.accessedStorageKeys
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame gasWarmAccess d)
    intro d'
    exact Devm.push_instructionFrame _ d'
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedStorageKey_instructionFrame d sevm.currentTarget key)
        (chargeGas_instructionFrame gasColdSload
          (addAccessedStorageKey d sevm.currentTarget key)))
    intro d'
    exact Devm.push_instructionFrame _ d'

lemma Rinst.pop_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .pop) := by
  simp only [Rinst.runCore]
  have hp := Devm.pop_instructionFrame pre
  cases h : pre.pop with
  | error e =>
      rw [h] at hp
      exact hp
  | ok x =>
      rcases x with ⟨word, d⟩
      rw [h] at hp
      simpa [h] using
        (Execution.Rel.trans_left Devm.instructionFrame_trans hp
          (chargeGas_instructionFrame gBase d))

lemma Rinst.dup_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 16) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.dup n)) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gVerylow pre)
  intro d
  cases h : d.stack[n]? with
  | none =>
      simp only
      exact Devm.instructionFrame_refl d
  | some word =>
      simp only
      exact Devm.push_instructionFrame word d

lemma Rinst.swap_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 16) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.swap n)) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gVerylow pre)
  intro d
  cases h : d.stack.swap n with
  | none =>
      simp only
      exact Devm.instructionFrame_refl d
  | some stack =>
      simp only
      exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma popNat3Bind_instructionFrame (pre : Devm)
    (next : Nat → Nat → Nat → Devm → Execution)
    (hnext : ∀ x y z d, Execution.Rel Devm.InstructionFrame d
      (next x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := next x y) ?_
  exact hnext x y

lemma popAdrNat3Bind_instructionFrame (pre : Devm)
    (next : Adr → Nat → Nat → Nat → Devm → Execution)
    (hnext : ∀ a x y z d, Execution.Rel Devm.InstructionFrame d
      (next a x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨a, d⟩ ← pre.popToAdr
      let ⟨x, d⟩ ← d.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToAdr_instructionFrame pre) (next := fun a d => do
      let ⟨x, d⟩ ← d.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro a d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := next a x y) ?_
  exact hnext a x y

lemma Rinst.retdatacopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .retdatacopy) := by
  simp only [Rinst.runCore]
  refine popNat3Bind_instructionFrame pre (next := fun memoryStart returnStart size d => do
    let d ← chargeGas
      (gVerylow + gReturnDataCopy * ceilDiv size 32 +
        d.extCost [(memoryStart, size)]) d
    if d.returnData.length < returnStart + size then
      .error ⟨.halt (.outOfBoundsRead .none), d⟩
    let value := d.returnData.sliceD returnStart size 0
    .ok (d.withMemory (d.memory.write memoryStart value))) ?_
  intro memoryStart returnStart size d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame
      (gVerylow + gReturnDataCopy * ceilDiv size 32 +
        d.extCost [(memoryStart, size)]) d)
  intro d'
  by_cases h : d'.returnData.length < returnStart + size
  · simp only [h, if_pos]
    exact Devm.instructionFrame_refl d'
  · simp only [h, if_false]
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma Rinst.extcodecopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodecopy) := by
  simp only [Rinst.runCore]
  refine popAdrNat3Bind_instructionFrame pre
    (next := fun a memoryStart codeStart size d =>
      if a ∈ d.accessedAddresses then do
        let d ← chargeGas (gasWarmAccess + gasCopy * ceilDiv size 32 +
          d.extCost [(memoryStart, size)]) d
        let value := (d.getCode a).sliceD codeStart size (Linst.toUInt8 .stop)
        .ok (d.withMemory (d.memory.write memoryStart value))
      else do
        let d ← chargeGas
          (gasColdAccountAccess + gasCopy * ceilDiv size 32 +
            d.extCost [(memoryStart, size)]) (addAccessedAddress d a)
        let value := (d.getCode a).sliceD codeStart size (Linst.toUInt8 .stop)
        .ok (d.withMemory (d.memory.write memoryStart value))) ?_
  intro a memoryStart codeStart size d
  by_cases h : a ∈ d.accessedAddresses
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame
        (gasWarmAccess + gasCopy * ceilDiv size 32 +
          d.extCost [(memoryStart, size)]) d)
    intro d'
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedAddress_instructionFrame d a)
        (chargeGas_instructionFrame
          (gasColdAccountAccess + gasCopy * ceilDiv size 32 +
            d.extCost [(memoryStart, size)])
          (addAccessedAddress d a)))
    intro d'
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma Rinst.log_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 5) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.log n)) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun memoryStart d => do
      let ⟨size, d⟩ ← d.popToNat
      let ⟨topics, d⟩ ← d.popN n
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro memoryStart d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun size d => do
      let ⟨topics, d⟩ ← d.popN n
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro size d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popN_instructionFrame d n) (next := fun topics d => do
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro topics d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  unfold assertDynamic Except.assert
  split
  · exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' memoryStart size)
      (Devm.addLog_instructionFrame (d'.memRead memoryStart size).2
        ⟨sevm.currentTarget, topics, (d'.memRead memoryStart size).1⟩)
  · exact Devm.instructionFrame_refl d'

theorem Rinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm r) := by
  cases r
  all_goals try contradiction
  all_goals try (
    with_reducible first
      | exact Rinst.exp_runCore_instructionFrame pc pre sevm
      | exact Rinst.kec_runCore_instructionFrame pc pre sevm
      | exact Rinst.balance_runCore_instructionFrame pc pre sevm
      | exact Rinst.blobhash_runCore_instructionFrame pc pre sevm
      | exact Rinst.calldataload_runCore_instructionFrame pc pre sevm
      | exact Rinst.calldatacopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.codecopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodesize_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodecopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.retdatacopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodehash_runCore_instructionFrame pc pre sevm
      | exact Rinst.blockhash_runCore_instructionFrame pc pre sevm
      | exact Rinst.pop_runCore_instructionFrame pc pre sevm
      | exact Rinst.mload_runCore_instructionFrame pc pre sevm
      | exact Rinst.mstore_runCore_instructionFrame pc pre sevm
      | exact Rinst.mstore8_runCore_instructionFrame pc pre sevm
      | exact Rinst.sload_runCore_instructionFrame pc pre sevm
      | exact Rinst.tload_runCore_instructionFrame pc pre sevm
      | exact Rinst.mcopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.gas_runCore_instructionFrame pc pre sevm
      | exact Rinst.clz_runCore_instructionFrame pc pre sevm
      | exact Rinst.dup_runCore_instructionFrame pc pre sevm _
      | exact Rinst.swap_runCore_instructionFrame pc pre sevm _
      | exact Rinst.log_runCore_instructionFrame pc pre sevm _)
  all_goals simp only [Rinst.runCore]
  all_goals with_reducible first
    | exact applyBinary_instructionFrame _ _ pre
    | exact applyTernary_instructionFrame _ _ pre
    | exact applyUnary_instructionFrame _ _ pre
    | exact pushItem_instructionFrame _ _ pre

lemma Devm.stateWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.StateWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state d'.state
      rw [hstate]
      rfl
    createdAccounts := hcreated, transientStorage := htransient }

/-- The state-writer frame implies the pre-existing `SSTORE` balance fact. -/
lemma Devm.StateWriteFrame.getBal_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getBal adr = d'.getBal adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.fst (congrFun hstate adr)

/-- The state-writer frame implies the pre-existing `SSTORE` code fact. -/
lemma Devm.StateWriteFrame.getCode_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getCode adr = d'.getCode adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.snd (congrFun hstate adr)

lemma Devm.setStorVal_stateWriteFrame (d : Devm)
    (adr : Adr) (key value : B256) :
    Devm.StateWriteFrame d (d.setStorVal adr key value) := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := rfl
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state (d.state.setStorVal adr key value)
      exact State.setStorVal_balCodeEq d.state adr key value
    createdAccounts := rfl, transientStorage := rfl }

lemma Devm.transientWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts) :
    Devm.TransientWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := hstate
    createdAccounts := hcreated, transientStorage := trivial }

lemma Rinst.tstore_runCore_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.runCore pc pre sevm .tstore) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (Devm.pop_instructionFrame pre)) (next := fun key d => do
        let ⟨value, d⟩ ← d.pop
        let d ← chargeGas gasWarmAccess d
        assertDynamic sevm d
        .ok (d.setTransVal sevm.currentTarget key value)) ?_
  intro key d
  refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (Devm.pop_instructionFrame d)) (next := fun value d => do
        let d ← chargeGas gasWarmAccess d
        assertDynamic sevm d
        .ok (d.setTransVal sevm.currentTarget key value)) ?_
  intro value d
  apply Execution.Rel.bind Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (chargeGas_instructionFrame gasWarmAccess d))
  intro d'
  unfold assertDynamic Except.assert
  split
  · exact Devm.transientWriteFrame_of_world_eq rfl rfl rfl
  · exact Devm.transientWriteFrame_refl d'

lemma Rinst.sstore_runCore_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.runCore pc pre sevm .sstore) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
      (Devm.pop_instructionFrame pre)) (next := fun key d => do
        let ⟨value, d⟩ ← d.pop
        .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
        let ct := sevm.currentTarget
        let original := getOrigStorVal sevm ct key
        let current := d.getStorVal ct key
        let ⟨d3, gas2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
            (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
        let gas3 ← .ok <|
          if original = current ∧ current ≠ value then
            if original = 0 then gas2 + gasStorageSet
            else gas2 + (gasStorageUpdate - gasColdSload)
          else gas2 + gasWarmAccess
        let d4 ← .ok <| d3.withRefundCounter
          (sstoreNewRefundCounter value original current d3.refundCounter)
        let d5 ← chargeGas gas3 d4
        assertDynamic sevm d5
        .ok (d5.setStorVal ct key value)) ?_
  intro key d
  refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
      (Devm.pop_instructionFrame d)) (next := fun value d => do
        .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
        let ct := sevm.currentTarget
        let original := getOrigStorVal sevm ct key
        let current := d.getStorVal ct key
        let ⟨d3, gas2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
            (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
        let gas3 ← .ok <|
          if original = current ∧ current ≠ value then
            if original = 0 then gas2 + gasStorageSet
            else gas2 + (gasStorageUpdate - gasColdSload)
          else gas2 + gasWarmAccess
        let d4 ← .ok <| d3.withRefundCounter
          (sstoreNewRefundCounter value original current d3.refundCounter)
        let d5 ← chargeGas gas3 d4
        assertDynamic sevm d5
        .ok (d5.setStorVal ct key value)) ?_
  intro value d
  unfold Except.assert
  dsimp only
  split
  · simp only [Except.bind_ok]
    let d3gas : Devm × Nat :=
      if (sevm.currentTarget, key) ∉ d.accessedStorageKeys then
        (addAccessedStorageKey d sevm.currentTarget key, gasColdSload)
      else (d, 0)
    let gas3 :=
      if getOrigStorVal sevm sevm.currentTarget key =
          d.getStorVal sevm.currentTarget key ∧
          d.getStorVal sevm.currentTarget key ≠ value then
        if getOrigStorVal sevm sevm.currentTarget key = 0 then
          d3gas.2 + gasStorageSet
        else d3gas.2 + (gasStorageUpdate - gasColdSload)
      else d3gas.2 + gasWarmAccess
    let d4 : Devm := d3gas.1.withRefundCounter (
      sstoreNewRefundCounter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (d.getStorVal sevm.currentTarget key) d3gas.1.refundCounter)
    change Execution.Rel Devm.StateWriteFrame d
      (chargeGas gas3 d4 >>= fun d5 =>
        assertDynamic sevm d5 >>= fun _ =>
          .ok (d5.setStorVal sevm.currentTarget key value))
    have hd4 : Devm.StateWriteFrame d d4 := by
      unfold d4 d3gas
      split <;> exact Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl
    apply Execution.Rel.bind Devm.stateWriteFrame_trans
      (Execution.Rel.trans_left Devm.stateWriteFrame_trans hd4
        (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
          (chargeGas_instructionFrame gas3 d4)))
    intro d5
    unfold assertDynamic Except.assert
    split
    · exact Devm.setStorVal_stateWriteFrame d5 sevm.currentTarget key value
    · exact Devm.stateWriteFrame_refl d5
  · exact Devm.stateWriteFrame_refl d

theorem Rinst.run_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ r) := by
  exact Rinst.runCore_instructionFrame pc sevm pre r
    h_not_sstore h_not_tstore

lemma Rinst.sstore_run_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .sstore) := by
  exact Rinst.sstore_runCore_stateWriteFrame pc pre sevm

lemma Rinst.tstore_run_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .tstore) := by
  exact Rinst.tstore_runCore_transientWriteFrame pc pre sevm

theorem Jinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame pre
      (Jinst.runCore pc pre sevm j) := by
  cases j <;> simp only [Jinst.runCore]
  case jump =>
    cases hp : pre.pop <;> simp only [Except.bind_error, Except.bind_ok]
    · have h := Devm.pop_instructionFrame pre
      rw [hp] at h
      exact h
    · rename_i x
      rcases x with ⟨dest, d⟩
      cases hg : chargeGas gMid d <;>
          simp only [Except.bind_error, Except.bind_ok]
      · exact Devm.instructionFrame_trans
          (by have h := Devm.pop_instructionFrame pre; rw [hp] at h; exact h)
          (by have h := chargeGas_instructionFrame gMid d; rw [hg] at h; exact h)
      · unfold Except.assert
        split <;> exact Devm.instructionFrame_trans
          (by have h := Devm.pop_instructionFrame pre; rw [hp] at h; exact h)
          (by have h := chargeGas_instructionFrame gMid d; rw [hg] at h; exact h)
  case jumpi =>
    cases hp1 : pre.pop <;> simp only [Except.bind_error, Except.bind_ok]
    · have h := Devm.pop_instructionFrame pre
      rw [hp1] at h
      exact h
    · rename_i x
      rcases x with ⟨dest, d1⟩
      have h1 := Devm.pop_instructionFrame pre
      rw [hp1] at h1
      cases hp2 : d1.pop <;> simp only [Except.bind_error, Except.bind_ok]
      · have h2 := Devm.pop_instructionFrame d1
        rw [hp2] at h2
        exact Devm.instructionFrame_trans h1 h2
      · rename_i y
        rcases y with ⟨cond, d2⟩
        have h2 := Devm.pop_instructionFrame d1
        rw [hp2] at h2
        have h12 := Devm.instructionFrame_trans h1 h2
        cases hg : chargeGas gHigh d2 <;>
            simp only [Except.bind_error, Except.bind_ok]
        · have h3 := chargeGas_instructionFrame gHigh d2
          rw [hg] at h3
          exact Devm.instructionFrame_trans h12 h3
        · rename_i d3
          have h3 := chargeGas_instructionFrame gHigh d2
          rw [hg] at h3
          have h123 := Devm.instructionFrame_trans h12 h3
          split
          · exact h123
          · unfold Except.assert
            split <;> exact h123
  case jumpdest =>
    cases hg : chargeGas gJumpdest pre <;>
        simp only [Except.bind_error, Except.bind_ok]
    · have h := chargeGas_instructionFrame gJumpdest pre
      rw [hg] at h
      exact h
    · have h := chargeGas_instructionFrame gJumpdest pre
      rw [hg] at h
      exact h

theorem Jinst.run_instructionFrame (evm : Evm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame evm.dyna
      (Jinst.run evm j) := by
  exact Jinst.runCore_instructionFrame evm.pc evm.sta evm.dyna j

theorem Linst.run_instructionFrame
    (sevm : Sevm) (pre : Devm) (l : Linst) (h_not_dest : l ≠ .dest) :
    Execution.Rel Devm.InstructionFrame pre (Linst.run sevm pre l) := by
  cases l <;> simp only [Linst.run]
  case stop => exact Devm.instructionFrame_refl pre
  case ret =>
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame pre)
      (next := fun index d => do
        let ⟨size, d⟩ ← d.popToNat
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .ok (d.withOutput output)) ?_
    intro index d
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame d)
      (next := fun size d => do
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .ok (d.withOutput output)) ?_
    intro size d
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (d.extCost [(index, size)]) d)
    intro d'
    exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' index size)
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  case rev =>
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame pre)
      (next := fun index d => do
        let ⟨size, d⟩ ← d.popToNat
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .error (.revert, d.withOutput output)) ?_
    intro index d
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame d)
      (next := fun size d => do
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .error (.revert, d.withOutput output)) ?_
    intro size d
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (d.extCost [(index, size)]) d)
    intro d'
    exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' index size)
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  case dest => contradiction

lemma Rinst.preserves_getCode
    {pc sevm devm r devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (hf.getCode_eq a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    simpa only [Devm.getCode, Devm.getAcct, id_eq] using congrFun (congrArg (fun s => fun a => (s.get a).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getCode a).symm

def Execution.getCode : Execution → Adr → ByteArray
  | Except.error ⟨_, devm⟩, adr => devm.getCode adr
  | Except.ok devm, adr => devm.getCode adr

lemma chargeGas_getCode_gen {cost devm exn} (h : chargeGas cost devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  cases exn with
  | error err => exact (chargeGas_worldEq_of_error h).getCode a |>.symm
  | ok devm' => exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma processCreateMessage.chargeCodeGas_getCode_gen {rules : ForkRules}
    {evm : Devm} {exn : Execution}
    (h : processCreateMessage.chargeCodeGas rules evm = exn) (a : Adr) :
    Execution.getCode exn a = evm.getCode a := by
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · subst h; rfl
  · dsimp [Bind.bind, Except.bind] at h
    split at h
    · rename_i eq_err; subst h
      have h_charge := chargeGas_getCode_gen eq_err a
      exact h_charge
    · rename_i eq_ok; split at h
      · subst h
        have h_charge := chargeGas_getCode_eq eq_ok a
        exact h_charge
      · subst h
        have h_charge := chargeGas_getCode_eq eq_ok a
        exact h_charge

lemma Devm.push_getCode_gen {v devm} {exn : Execution} (h : Devm.push v devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  subst h
  cases hp : Devm.push v devm with
  | error err =>
    exact (liftMachExecution_worldEq_of_error (core := Mach.push v) hp).getCode a |>.symm
  | ok d =>
    exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) hp).getCode a |>.symm

def Xlot.InvGetCode : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ =>
    ∀ adr,
      (evm.dyna.getCode adr).toList ≠ [] →
      evm.dyna.getCode adr = Execution.getCode exn adr

lemma applyPrecompResult_getCode (evm : Evm) (res : PrecompResult) (ex : Execution)
    (h_ex : applyPrecompResult evm res = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a := by
  revert h_ex
  cases res <;> (intro h_ex; subst h_ex; rfl)

lemma executePrecomp_preserves_getCode (evm : Evm) (adr : Adr) (ex : Execution)
    (h_ex : executePrecomp evm adr = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a := by
  apply applyPrecompResult_getCode evm (precompileRun evm adr) ex h_ex a

def MsgResult.getCode (exn : Except (EvmError × State × AdrSet × Tra) Devm) (a : Adr) : ByteArray :=
  match exn with
  | .ok d => d.getCode a
  | .error ⟨_, state, _, _⟩ => state.getCode a

/-! ## Step 7.2 — message-level code-effect masters

Relational code-preservation over message results.  `CodePreserve` says every
nonempty-code address is left untouched; `CodePreserveExcept w` weakens that by
also excluding the single write target `w` (the freshly-created contract). -/

def MsgResult.CodePreserve (base : State)
    (exn : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → MsgResult.getCode exn a = base.getCode a

def MsgResult.CodePreserveExcept (base : State) (w : Adr)
    (exn : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, a ≠ w → (base.getCode a).toList ≠ [] →
    MsgResult.getCode exn a = base.getCode a

/-- Relational code-preservation over an `Execution` outcome (used by the
Step 7.3 generic-operation masters): every nonempty-code address of `base` has
the same code in the result, on both the ok and error branches. -/
def Execution.CodePreserve (base : Devm) (exn : Execution) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → Execution.getCode exn a = base.getCode a

/-- Writer leaf: `handleError` reshuffles error payloads into ok results and
selects states, but never installs new code. -/
lemma executeCode.handleError_getCode (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleError exn) a = Execution.getCode exn a := by
  cases exn with
  | ok d => rfl
  | error p =>
    rcases p with ⟨err, evm⟩
    cases err <;> rfl

/-- Writer leaf: rollback installs the selected state, so its code map is that
state's code map. -/
lemma Devm.rollback_getCode (devm : Devm) (st : State) (tra : Tra) (a : Adr) :
    (devm.rollback st tra).getCode a = st.getCode a := rfl

/-- **Frame-level state restoration.**  A message frame that settles `.ok` with
its error flag set has had its world rolled back to the values `msg` entered
with: `msg.benv.state` and `msg.tenv.transientStorage`.

**The frame named is `msg`'s own**, and naming it is the whole content of the
statement.  This is *not* "the transaction was rolled back", which would be a
different and often false claim — a failed inner call can be caught by its
caller while the surrounding transaction succeeds, and this theorem is
deliberately silent about every frame but `msg`'s.

**No error kind is named, and none can be.**  The hypothesis is
`out.error.isSome` and nothing more.  Two reasons, and both are load-bearing:
the settled error is `.ok`-level only, so nothing about *which* error occurred
survives the frame boundary; and a claim naming a failure shape would be
coupled to compiled bytes that this shared-layer lemma has no business knowing.

**This is not liveness and not a claim that any frame ever fails.**  Both
`ProcessMessage msg xl (.ok out)` and `out.error.isSome` are hypotheses.  The
theorem rules a world-state *in* given a settled error; it says nothing about
whether any particular message reaches one.

The mechanism is `processMessage.settle`, whose rollback arm installs exactly
these two components (`Devm.rollback` writes `world` and nothing else, so the
error flag it is conditioned on survives it untouched).  No slot derivation is
involved: the `out.error.isSome` hypothesis selects the rollback arm on its
own, which is why this needs neither `Xlot.Filled` nor anything above it. -/
theorem ProcessMessage.rollback_of_error {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome) :
    out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  obtain ⟨r0, -, hset⟩ := ProcessMessage.iff_body.mp h
  rcases r0 with x | evm'
  -- `processMessage.settle_error` says exactly this, but it is declared far
  -- below in this file; the settle of an `.error` reduces on its own.
  · cases hset
  unfold processMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  by_cases herr' : evm'.error.isSome = true
  · rw [if_pos herr'] at hset
    rw [Except.ok.inj hset]
    exact ⟨rfl, rfl⟩
  · rw [if_neg herr'] at hset
    exact absurd (Except.ok.inj hset ▸ herr) herr'

/-- A clean retained child message installs exactly the committed raw child's
world state.  Message settlement changes only wrapper metadata on this path. -/
theorem ProcessMessage.ok_state_eq_committedPost
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hcommit : Execution.commits out = true) :
    post.state = (Execution.committedPost out hcommit).state := by
  have hsettle := (RunFrame.some_inv hprocess).2
  cases out with
  | error err =>
      simp [Execution.commits] at hcommit
  | ok raw =>
      simp only [Execution.commits] at hcommit
      cases herr : raw.error with
      | none =>
          simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
            executeCode.handleError, processMessage.settle, herr] at hsettle
          exact congrArg Devm.state hsettle
      | some error =>
          simp [herr] at hcommit

/-- A raw child execution that does not commit is rolled back to the message
entry world before its parent resumes. -/
theorem ProcessMessage.ok_state_eq_of_not_commits
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hnot : Execution.commits out ≠ true) :
    post.state = msg.benv.state := by
  have hsettle := (RunFrame.some_inv hprocess).2
  cases out with
  | error err =>
      rcases err with ⟨error, raw⟩
      cases error with
      | halt reason =>
          rcases (show ∃ handled : Devm,
              executeCode.handleError (.error (.halt reason, raw)) =
                .ok handled ∧ handled.error.isSome = true by
                simp [executeCode.handleError, Devm.error,
                  Devm.setMeta]) with ⟨handled, hhandle, hhandled⟩
          have hsettle' :
              (.ok post) = processMessage.settle msg (.ok handled) := by
            simpa [Frame.ofCall, Frame.settle, Frame.settleMsg,
              hhandle] using hsettle
          unfold processMessage.settle at hsettle'
          simp only [bind, Except.bind] at hsettle'
          rw [if_pos hhandled] at hsettle'
          have heq := Except.ok.inj hsettle'
          calc
            post.state =
                (handled.rollback msg.benv.state
                  msg.tenv.transientStorage).state :=
              congrArg Devm.state heq
            _ = msg.benv.state := rfl
      | revert =>
          rcases (show ∃ handled : Devm,
              executeCode.handleError (.error (.revert, raw)) =
                .ok handled ∧ handled.error.isSome = true by
                simp [executeCode.handleError, Devm.error,
                  Devm.withError, Devm.setMeta]) with
            ⟨handled, hhandle, hhandled⟩
          have hsettle' :
              (.ok post) = processMessage.settle msg (.ok handled) := by
            simpa [Frame.ofCall, Frame.settle, Frame.settleMsg,
              hhandle] using hsettle
          unfold processMessage.settle at hsettle'
          simp only [bind, Except.bind] at hsettle'
          rw [if_pos hhandled] at hsettle'
          have heq := Except.ok.inj hsettle'
          calc
            post.state =
                (handled.rollback msg.benv.state
                  msg.tenv.transientStorage).state :=
              congrArg Devm.state heq
            _ = msg.benv.state := rfl
      | crypto reason =>
          simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
            executeCode.handleError, processMessage.settle] at hsettle
      | internal reason =>
          simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
            executeCode.handleError, processMessage.settle] at hsettle
  | ok raw =>
      cases herr : raw.error with
      | none =>
          simp [Execution.commits, herr] at hnot
      | some error =>
          simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
            executeCode.handleError, processMessage.settle, herr] at hsettle
          exact congrArg Devm.state hsettle

/-- Handling a synchronous precompile result preserves the message-entry world
state; precompiles only determine gas, output, and error metadata. -/
theorem executeCode.handle_precompile_ok_state
    {msg : Msg} {address : Adr} {post : Devm}
    (h : executeCode.handleError
        (executePrecomp (initEvm msg) address) = .ok post) :
    post.state = msg.benv.state := by
  unfold executePrecomp applyPrecompResult at h
  cases hpre : precompileRun (initEvm msg) address with
  | error error cost =>
      simp only [hpre] at h
      cases error <;> simp [executeCode.handleError] at h
      · exact (congrArg Devm.state h).symm.trans rfl
      · exact (congrArg Devm.state h).symm.trans rfl
  | ok cost output =>
      simp [hpre, executeCode.handleError] at h
      exact (congrArg Devm.state h).symm.trans rfl

/-- Successful CREATE code-gas charging preserves the frame error marker. -/
theorem processCreateMessage.chargeCodeGas_error_eq
    {rules : ForkRules} {pre post : Devm}
    (h : processCreateMessage.chargeCodeGas rules pre = .ok post) :
    post.error = pre.error := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h
  · rcases Except.bind_eq_ok h with ⟨charged, hcharge, hrest⟩
    split at hrest
    · cases hrest
    · cases hrest
      rw [chargeGas_def] at hcharge
      split at hcharge
      · cases hcharge
      · cases hcharge
        rfl

/-- A CREATE frame that settles with its error marker set restores the world
saved at CREATE-message entry, including code-deposit failure. -/
theorem ProcessCreateMessage.rollback_of_error
    {msg : Msg} {slot : Xlot} {post : Devm}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = true) :
    post.state = msg.benv.state := by
  rcases ProcessCreateMessage.iff_processMessage.mp hprocess with
    ⟨result, _hinner, hsettle⟩
  cases result with
  | error error =>
      simp [processCreateMessage.settle] at hsettle
  | ok inner =>
      unfold processCreateMessage.settle at hsettle
      simp only [bind, Except.bind] at hsettle
      by_cases hinnerNone : inner.error.isNone = true
      · rw [if_pos hinnerNone] at hsettle
        cases hcharge :
          processCreateMessage.chargeCodeGas
            msg.benv.stat.rules inner with
        | error error =>
            rw [hcharge] at hsettle
            rcases error with ⟨error, charged⟩
            cases error with
            | halt reason =>
                have heq := Except.ok.inj hsettle
                calc
                  post.state =
                      (processCreateMessage.exceptionalHalt charged reason
                        msg.benv.state msg.tenv.transientStorage).state :=
                    congrArg Devm.state heq
                  _ = msg.benv.state := rfl
            | revert => cases hsettle
            | crypto reason => cases hsettle
            | internal reason => cases hsettle
        | ok charged =>
            rw [hcharge] at hsettle
            simp only [Except.ok.injEq] at hsettle
            have hchargedError :=
              processCreateMessage.chargeCodeGas_error_eq hcharge
            cases hinner : inner.error <;>
              simp [hinner] at hinnerNone hchargedError
            rw [hsettle] at herror
            change charged.error.isSome = true at herror
            simp [hchargedError] at herror
      · rw [if_neg hinnerNone] at hsettle
        have heq := Except.ok.inj hsettle
        calc
          post.state =
              (inner.rollback msg.benv.state
                msg.tenv.transientStorage).state :=
            congrArg Devm.state heq
          _ = msg.benv.state := rfl

/-- Writer leaf: value transfer changes balances but preserves code. -/
lemma benvAfterTransfer_ok_getCode {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Adr) :
    benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h
  split at h
  · cases h_sub : msg.benv.subBal msg.caller msg.value with
    | none => simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h
    | some benv_sub =>
      simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h
      subst benv
      rw [Benv.addBal_getCode]
      exact Benv.subBal_getCode h_sub
  · simp only [Except.ok.injEq] at h; subst benv; rfl

/-- Writer leaf: create preparation (nonce bump, created-account marking, empty
storage) preserves code. -/
lemma processCreateMessage.msg_getCode (msg : Msg) (a : Adr) :
    (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp [processCreateMessage.msg, Msg.withBenv]
  rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]

/-- Master: `executeCode` preserves the code of every nonempty-code address.
The suspended child's oracle invariant (`inv`) supplies the interpreted-code
case; `handleError_getCode` covers precompile and error selection. -/
lemma ExecuteCode.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ExecuteCode msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a ha
  unfold ExecuteCode at run
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at run
  · rcases run with ⟨raw, h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleError_getCode]
    rw [h_xl] at inv
    dsimp [Xlot.InvGetCode] at inv
    rw [executeCode.enter_inl henter] at inv
    exact (inv a ha).symm
  · rcases run with ⟨h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleError_getCode]
    obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    rw [hraw]
    exact executePrecomp_preserves_getCode (initEvm msg) adr _ rfl a

lemma ProcessMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a ha
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with e | benv <;> rw [h_benv] at hbody
  · rw [hbody.2]
    dsimp [MsgResult.getCode, processMessage.settle]
    dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv
    split at h_benv
    · cases h_sub : msg.benv.subBal msg.caller msg.value
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
        subst h_benv
        rfl
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
    · contradiction
  · have h_benv_code := benvAfterTransfer_ok_getCode h_benv a
    have ha' : ( (msg.withBenv benv).benv.state.getCode a ).toList ≠ [] := by
      dsimp [Msg.withBenv]
      rw [h_benv_code]
      exact ha
    have h_exec_cond := ExecuteCode.codePreserve inv hbody a ha'
    dsimp [Msg.withBenv] at h_exec_cond
    rw [h_benv_code] at h_exec_cond
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact h_exec_cond
    · dsimp only [bind, Except.bind]
      split
      · exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a
      · exact h_exec_cond

lemma ProcessMessage.preserves_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a :=
  ProcessMessage.codePreserve inv run

lemma setCode_getCode {evm : Devm} {a b : Adr} {code : ByteArray} (h : a ≠ b) :
  (evm.setCode a code).getCode b = evm.getCode b := by
  dsimp [Devm.setCode, Devm.withState, Devm.setWorld, Devm.world,
    Devm.getCode, Devm.state, Devm.getAcct, State.setCode, State.set,
    State.getCode, State.get]
  split_ifs with h_if
  · by_cases hc : compare a b = Ordering.eq
    · exact False.elim (h (compare_eq_iff_eq.mp hc))
    · rw [Std.TreeMap.getD_erase]
      simp [hc]
  · by_cases hc : compare a b = Ordering.eq
    · exact False.elim (h (compare_eq_iff_eq.mp hc))
    · rw [Std.TreeMap.getD_insert]
      simp [hc]

/-- Master: `processCreateMessage` preserves the code of every nonempty-code
address *other than* the create target.  Create preparation
(`processCreateMessage.msg_getCode`) and the interpreted body
(`ProcessMessage.codePreserve`) preserve code; code-gas charging preserves it
(`chargeCodeGas_getCode_gen`); create completion writes only `msg.currentTarget`
through `setCode` (`setCode_getCode`, excluded by `a ≠ msg.currentTarget`); the
halt/error paths select states via rollback (`Devm.rollback_getCode`). -/
lemma ProcessCreateMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl exn) :
    MsgResult.CodePreserveExcept msg.benv.state msg.currentTarget exn := by
  intro a h_a ha
  have h_benv_code := processCreateMessage.msg_getCode msg a
  have ha' : ((processCreateMessage.msg msg).benv.state.getCode a).toList ≠ [] := by
    rw [h_benv_code]; exact ha
  obtain ⟨ex', h_exec, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_exec_cond := ProcessMessage.codePreserve inv h_exec a ha'
  rw [h_benv_code] at h_exec_cond
  unfold processCreateMessage.settle
  rcases ex' with x | evm
  · exact h_exec_cond
  · dsimp only [bind, Except.bind]
    split
    · rename_i h_none
      cases h_charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        change err_evm.state.getCode a = evm.state.getCode a at h_getCode
        cases err_msg <;>
          simp only [MsgResult.getCode, processCreateMessage.exceptionalHalt] <;>
          first
            | rfl
            | (rw [h_getCode]; exact h_exec_cond)
      | ok devm_charge =>
        dsimp only [MsgResult.getCode]
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        dsimp [Execution.getCode] at h_getCode
        rw [setCode_getCode h_a.symm]
        rw [h_getCode]
        exact h_exec_cond
    · rename_i h_some
      exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a

lemma createMsg_benv_state_getCode
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} (a : Adr) :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.state.getCode a
      = devm.getCode a := rfl

/-- The CREATE-family return path preserves code at every address other than
the freshly created one, given the child frame preserved it. -/
lemma Resume.create_getCode {parent : Devm} {newAddress a : Adr}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode ((Resume.create parent newAddress).run r) a =
      parent.getCode a := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    change state.getCode a = parent.getCode a
    exact h
  · dsimp only [MsgResult.getCode] at h
    split
    · rw [Devm.push_getCode_gen rfl a]
      dsimp only [incorporateChildOnError]
      exact h
    · rw [Devm.push_getCode_gen rfl a]
      dsimp only [incorporateChildOnSuccess]
      exact h

lemma GenericCreate.codePreserve
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : xl.InvGetCode)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    Execution.CodePreserve devm exn := by
  intro a ha
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    rfl
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    rfl
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    rename_i h_collision
    have h_parent : ∀ b : Adr,
        (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode b = devm.getCode b := by
      intro b
      rw [addAccessedAddress_getCode]
      exact Devm.incrNonce_getCode
    have h_a_ne : a ≠ newAddress := by
      intro h_eq
      push Not at h_collision
      have h_code_size : ((addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode newAddress).size = 0 :=
        h_collision.2.1
      have h_empty : devm.getCode newAddress = .empty := by
        rw [← h_parent newAddress]
        cases h_code' : (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode newAddress with
        | mk data =>
          rw [h_code'] at h_code_size
          cases data with
          | mk l =>
            cases l
            · rfl
            · contradiction
      rw [h_eq, h_empty] at ha
      exact ha (by unfold ByteArray.toList ByteArray.toList.loop; rfl)
    rw [Resume.create_getCode ?_, h_parent a]
    exact ProcessCreateMessage.codePreserve inv hframe a h_a_ne
      (by rw [createMsg_benv_state_getCode, h_parent a]; exact ha)

lemma callMsg_benv_state_getCode
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {calldata : Bytes} {code : ByteArray} {disablePrecompiles : Bool} (a : Adr) :
    ( callMsg sevm evm1 gas value caller target codeAddress shouldTransferValue
        isStaticcall calldata code disablePrecompiles ).benv.state.getCode a
      = evm1.getCode a := rfl

/-- The CALL-family return path preserves code at every address, given the child
frame preserved it: `memWrite` touches memory only, and `incorporateChild*`
installs the child's state, whose code map the child preserved. -/
lemma Resume.call_getCode {parent : Devm} {a : Adr} {outputIndex outputSize : Nat}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode ((Resume.call parent outputIndex outputSize).run r) a =
      parent.getCode a := by
  have hmw : ∀ (d : Devm) (o : Bytes),
      (d.memWrite outputIndex o).getCode a = d.getCode a := fun d o =>
    (liftMachPure_worldEq (Mach.memWrite · outputIndex o) d).getCode a |>.symm
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    change state.getCode a = parent.getCode a
    exact h
  · dsimp only [MsgResult.getCode] at h
    split
    · rcases hpush : (incorporateChildOnError parent child child.output).push 0 with
        e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
      · exact hp.trans h
      · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
        rw [hmw]
        exact hp.trans h
    · rcases hpush : (incorporateChildOnSuccess parent child child.output).push 1 with
        e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
      · exact hp.trans h
      · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
        rw [hmw]
        exact hp.trans h

/-- On the successful path the CREATE-family return installs the child's
world; the status push leaves it alone. -/
lemma Resume.create_state {parent child : Devm} {newAddress : Adr} {sf : Devm}
    (h : (Resume.create parent newAddress).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256,
      Devm.push v d = .ok sf → sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rw [hh] at hframe
    have hframe' : Devm.InstructionFrame d sf := hframe
    rw [← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child []) rfl _ h

/-- A failed child message aborts the CALL-family return path. -/
lemma Resume.call_run_error {parent : Devm} {oi os : Nat}
    {e : EvmError × Jaune.State × AdrSet × Tra} {sf : Devm}
    (h : (Resume.call parent oi os).run (.error e) = .ok sf) : False := by
  rcases e with ⟨err, st, ac, tra⟩
  unfold Resume.run liftToExecution at h
  cases h

/-- On the successful path the CALL-family return installs the child's world;
the status push and the memory write leave it alone. -/
lemma Resume.call_state {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh hframe
    · cases hh
    · injection hh with hh
      subst hh
      have hframe' : Devm.InstructionFrame d evm2 := hframe
      rw [← (Devm.memWrite_instructionFrame evm2 oi (child.output.take os)).state,
        ← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

lemma GenericCall.codePreserve
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : xl.InvGetCode)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    Execution.CodePreserve devm exn := by
  intro a ha
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    rw [Resume.call_getCode ?_]
    · rfl
    · rw [ProcessMessage.codePreserve inv hframe a
        (by rw [callMsg_benv_state_getCode]; exact ha)]
      exact callMsg_benv_state_getCode a

/-- A call-type step whose `Except` prefix failed carries that failure. -/
lemma XStep.run_ofExcept_error {e : EvmError × Devm} {xl : Xlot} {ex : Execution}
    (h : XStep.Run (XStep.ofExcept (.error e)) xl ex) : ex = .error e := h.2

/-! ### The dispatch shape of a call-type instruction

Everything `Xinst.step` does before dispatching — popping operands, charging
gas, extending memory, recording accesses, resolving delegations — stays inside
the instruction frame.  Recording that once, together with the two dispatch
targets and the provenance of the child's code, is what replaces the six
per-constructor bind walks the old mirrors forced: every `Xinst`-level master
below is a three-case argument over `Shape`. -/

def Xinst.Shape (sevm : Sevm) (devm : Devm) (s : XStep) : Prop :=
  (∃ ex, s = .done ex ∧ Execution.Rel Devm.InstructionFrame devm ex) ∨
  (∃ d endowment newAddress mi ms,
      Devm.InstructionFrame devm d ∧
      s = genericCreate.step sevm d endowment newAddress mi ms) ∨
  (∃ d d₀ gas value caller target codeAddress stv isSt ii isz oi osz code dp,
      Devm.InstructionFrame devm d ∧
      Devm.InstructionFrame devm d₀ ∧
      ( (stv = true ∧ caller = sevm.currentTarget) ∨
        (stv = false ∧ target = sevm.currentTarget) ) ∧
      ( target = sevm.currentTarget ∨
        ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target ) ) ∧
      s = genericCall.step sevm d gas value caller target codeAddress stv isSt
            ii isz oi osz code dp)

lemma Xinst.Shape.trans_left {sevm : Sevm} {a b : Devm} {s : XStep}
    (hab : Devm.InstructionFrame a b) (h : Xinst.Shape sevm b s) :
    Xinst.Shape sevm a s := by
  rcases h with ⟨ex, rfl, hex⟩ | ⟨d, e, na, mi, ms, hf, rfl⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, hf₀, hcal, hsrc, rfl⟩
  · exact Or.inl ⟨ex, rfl,
      Execution.Rel.trans_left Devm.instructionFrame_trans hab hex⟩
  · exact Or.inr (Or.inl ⟨d, e, na, mi, ms,
      Devm.instructionFrame_trans hab hf, rfl⟩)
  · exact Or.inr (Or.inr ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz,
      code, dp, Devm.instructionFrame_trans hab hf,
      Devm.instructionFrame_trans hab hf₀, hcal, hsrc, rfl⟩)

lemma Xinst.shape_done {sevm : Sevm} {devm : Devm} {ex : Execution}
    (h : Execution.Rel Devm.InstructionFrame devm ex) :
    Xinst.Shape sevm devm (.done ex) := Or.inl ⟨ex, rfl, h⟩

lemma Xinst.shape_error {sevm : Sevm} {devm : Devm} {err : EvmError × Devm}
    (h : Devm.InstructionFrame devm err.2) :
    Xinst.Shape sevm devm (XStep.ofExcept (.error err)) := Xinst.shape_done h

lemma Xinst.shape_create {sevm : Sevm} {devm d : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (genericCreate.step sevm d endowment newAddress mi ms) :=
  Or.inr (Or.inl ⟨d, endowment, newAddress, mi, ms, hf, rfl⟩)

lemma Xinst.shape_call {sevm : Sevm} {devm d d₀ : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp : Bool}
    (hf : Devm.InstructionFrame devm d) (hf₀ : Devm.InstructionFrame devm d₀)
    (hcal : (stv = true ∧ caller = sevm.currentTarget) ∨
      (stv = false ∧ target = sevm.currentTarget))
    (hsrc : target = sevm.currentTarget ∨
      ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target )) :
    Xinst.Shape sevm devm
      (genericCall.step sevm d gas value caller target codeAddress stv isSt
        ii isz oi osz code dp) :=
  Or.inr (Or.inr ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt,
    ii, isz, oi, osz, code, dp, hf, hf₀, hcal, hsrc, rfl⟩)

lemma Xinst.shape_bind {sevm : Sevm} {devm d : Devm} {α : Type}
    {x : Except (EvmError × Devm) (α × Devm)}
    {f : α × Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d x)
    (hf : ∀ (v : α) (d' : Devm), Devm.InstructionFrame devm d' →
      Xinst.Shape sevm devm (XStep.ofExcept (f ⟨v, d'⟩))) :
    Xinst.Shape sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | ⟨v, d'⟩
  · exact Xinst.shape_error (Devm.instructionFrame_trans hd hx)
  · exact hf v d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shape_bindE {sevm : Sevm} {devm d : Devm} {x : Execution}
    {f : Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Execution.Rel Devm.InstructionFrame d x)
    (hf : ∀ d' : Devm, Devm.InstructionFrame devm d' →
      Xinst.Shape sevm devm (XStep.ofExcept (f d'))) :
    Xinst.Shape sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | d'
  · exact Xinst.shape_error (Devm.instructionFrame_trans hd hx)
  · exact hf d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shape_assert {sevm : Sevm} {devm : Devm} {p : Prop} [Decidable p]
    {err : EvmError × Devm} {f : Unit → Except (EvmError × Devm) XStep}
    (herr : Devm.InstructionFrame devm err.2)
    (hf : Xinst.Shape sevm devm (XStep.ofExcept (f ()))) :
    Xinst.Shape sevm devm (XStep.ofExcept (Except.assert p err >>= f)) := by
  unfold Except.assert
  split
  · exact hf
  · exact Xinst.shape_error herr

/-- The early exit taken when the caller cannot cover the transferred value:
a push onto a machine whose world is untouched. -/
lemma Xinst.shape_shortfall {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withReturnData []).withGasLeft
            (d'.gasLeft + stipend)))))) := by
  refine Xinst.shape_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shape_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))

lemma Xinst.shape_shortfall' {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withGasLeft
            (d'.gasLeft + stipend)).withReturnData []))))) := by
  refine Xinst.shape_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shape_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))

/-- Delegation resolution is the identity when the callee is not a delegating
EOA, so the child's code is exactly the callee's own code. -/
lemma accessDelegation_of_not_delegation {d : Devm} {adr : Adr}
    (h : ¬ isValidDelegation (d.getCode adr)) :
    accessDelegation d adr = ⟨false, adr, d.getCode adr, 0, d⟩ := by
  have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := by
    dsimp only [getDelegatedCodeAddress]
    rw [if_neg (show ¬ isValidDelegation (d.state.getCode adr) from h)]
  dsimp only [accessDelegation]
  rw [hnone]
  rfl

lemma Xinst.step_shape (sevm : Sevm) (devm : Devm) (x : Xinst) :
    Xinst.Shape sevm devm (Xinst.step sevm devm x) := by
  cases x with
  | create =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bindE h3 (chargeGas_instructionFrame _ d3) fun d4 h4 => ?_
    exact Xinst.shape_create
      (Devm.instructionFrame_trans h4 (Devm.memExtends_instructionFrame d4 _))
  | create2 =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.pop_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bindE h4 (chargeGas_instructionFrame _ d4) fun d5 h5 => ?_
    exact Xinst.shape_create
      (Devm.instructionFrame_trans h5 (Devm.memExtends_instructionFrame d5 _))
  | call =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun callee d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
    have h7' : Devm.InstructionFrame devm (addAccessedAddress d7 callee) :=
      Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 callee)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d7 callee) callee
    rcases hdel : accessDelegation (addAccessedAddress d7 callee) callee with
      ⟨dpv, na, cd, dagc, d8⟩
    rw [hdel] at hacc
    have h8 : Devm.InstructionFrame devm d8 :=
      Devm.instructionFrame_trans h7' hacc
    refine Xinst.shape_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
    refine Xinst.shape_assert h9 ?_
    split
    · exact Xinst.shape_shortfall
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
    · refine Xinst.shape_call
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
        h7' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
      rw [accessDelegation_of_not_delegation hnd] at hdel
      exact (congrArg (fun t => t.2.2.1) hdel).symm
  | callcode =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun cadr d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
    have h7' : Devm.InstructionFrame devm (addAccessedAddress d7 cadr) :=
      Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 cadr)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d7 cadr) cadr
    rcases hdel : accessDelegation (addAccessedAddress d7 cadr) cadr with
      ⟨dpv, na, cd, dagc, d8⟩
    rw [hdel] at hacc
    have h8 : Devm.InstructionFrame devm d8 :=
      Devm.instructionFrame_trans h7' hacc
    refine Xinst.shape_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
    split
    · exact Xinst.shape_shortfall'
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
    · exact Xinst.shape_call
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
        h7' (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
  | delcall =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun cadr d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    have h6' : Devm.InstructionFrame devm (addAccessedAddress d6 cadr) :=
      Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 cadr)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d6 cadr) cadr
    rcases hdel : accessDelegation (addAccessedAddress d6 cadr) cadr with
      ⟨dpv, na, cd, dagc, d7⟩
    rw [hdel] at hacc
    have h7 : Devm.InstructionFrame devm d7 :=
      Devm.instructionFrame_trans h6' hacc
    refine Xinst.shape_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
    exact Xinst.shape_call
      (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
      h6' (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
  | statcall =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun tgt d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    have h6' : Devm.InstructionFrame devm (addAccessedAddress d6 tgt) :=
      Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 tgt)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d6 tgt) tgt
    rcases hdel : accessDelegation (addAccessedAddress d6 tgt) tgt with
      ⟨dpv, na, cd, dagc, d7⟩
    rw [hdel] at hacc
    have h7 : Devm.InstructionFrame devm d7 :=
      Devm.instructionFrame_trans h6' hacc
    refine Xinst.shape_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
    refine Xinst.shape_call
      (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
      h6' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
    rw [accessDelegation_of_not_delegation hnd] at hdel
    exact (congrArg (fun t => t.2.2.1) hdel).symm

/-! ### What a spawned child frame starts from

`Prog.At` bookkeeping has to survive a suspension: the child's initial machine
must still see the contract's code, and — when the child *is* the contract —
must start at `pc = 0` with that code loaded.  With the interpreter flattened
all of this is read off the frame-entry equation plus one dispatch-level case
split, which is what the old six-lemma `prep_*` family did by hand. -/

lemma ByteArray.eq_empty_of_size_eq_zero {b : ByteArray} (h : b.size = 0) :
    b = .empty := by
  cases b with
  | mk data =>
    cases data with
    | mk l =>
      cases l with
      | nil => rfl
      | cons _ _ => contradiction

lemma Frame.enter_run_pc {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.pc = 0 := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_code {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.sta.code = f.inner.code := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_currentTarget {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) :
    cevm.sta.currentTarget = f.inner.currentTarget := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_getCode {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) (a : Adr) :
    cevm.dyna.getCode a = f.inner.benv.state.getCode a := by
  obtain ⟨benv, hbenv, rfl⟩ := Frame.enter_run_inv h
  exact benvAfterTransfer_ok_getCode hbenv a

lemma genericCreate.step_spawn_frame
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress mi ms
      = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = newAddress ∧
      devm.getCode newAddress = .empty := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rename_i h_collision
  have hpar : ∀ b : Adr,
      (addAccessedAddress
        (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress).getCode b
        = devm.getCode b := by
    intro b
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  refine ⟨fun a => ?_, rfl, ?_⟩
  · simp only [Frame.ofCreate]
    rw [processCreateMessage.msg_getCode, createMsg_benv_state_getCode]
    exact hpar a
  · push Not at h_collision
    rw [← hpar newAddress]
    exact ByteArray.eq_empty_of_size_eq_zero h_collision.2.1

lemma genericCall.step_spawn_frame
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = target ∧ f.inner.code = code := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  exact ⟨fun _ => rfl, rfl, rfl⟩

lemma Xinst.step_spawn_getCode {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm)
    (a : Adr) : f.inner.benv.state.getCode a = devm.getCode a := by
  rcases Xinst.step_shape sevm devm x with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · rw [(genericCreate.step_spawn_frame hs).1 a, hf.getCode a]
  · rw [(genericCall.step_spawn_frame hs).1 a, hf.getCode a]

/-- Delegation resolution is the identity on an address whose code carries no
EIP-7702 designator, so the resolved code address is the queried address. -/
private lemma accessDelegation_codeAddress_of_none {d : Devm} {adr : Adr}
    (h : getDelegatedCodeAddress (d.getCode adr) = none) :
    (accessDelegation d adr).2.1 = adr := by
  dsimp only [accessDelegation]
  rw [show getDelegatedCodeAddress (d.state.getCode adr) = none from h]

/-- An actual call-type spawn aimed away from the current account and at an
already-code-bearing account is a direct CALL/STATICCALL child. CREATE and
CREATE2 are excluded by freshness, while CALLCODE and DELEGATECALL retain the
parent's target. The CALL/STATICCALL arms additionally need the callee to carry
no EIP-7702 delegation designator: a designator would resolve the child's code
address to the delegate rather than to the callee. -/
theorem Xinst.step_spawn_codeAddress_eq_currentTarget
    {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hne : sevm.currentTarget ≠ f.inner.currentTarget)
    (hcode : devm.getCode f.inner.currentTarget ≠ .empty)
    (hnodel :
      getDelegatedCodeAddress (devm.getCode f.inner.currentTarget) = none) :
    f.inner.codeAddress = some f.inner.currentTarget := by
  have horig := hs
  cases x with
  | create =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have hfresh := genericCreate.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
  | create2 =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have hfresh := genericCreate.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
  | call =>
      simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hs
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vgas hgas
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vcallee hcallee
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vval hval
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vii hii
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vis his
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ voi hoi
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vos hos
      -- The delegation lookup runs on the popped-and-recorded machine, so the
      -- premise's code fact has to travel down the operand pops first.
      have hgc : ∀ a : Adr,
          (addAccessedAddress vos.2 vcallee.1).getCode a = devm.getCode a := by
        intro a
        rw [addAccessedAddress_getCode, Devm.popToNat_getCode hos,
          Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
          Devm.popToNat_getCode hii, Devm.pop_getCode hval,
          Devm.popToAdr_getCode hcallee, Devm.pop_getCode hgas]
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
            Except.pure] at hs
          repeat' split at hs
          all_goals
            simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
          all_goals obtain ⟨rfl, rfl⟩ := hs
          all_goals
            refine congrArg some (accessDelegation_codeAddress_of_none ?_)
            rw [hgc]
            exact hnodel
  | callcode =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have htgt := (genericCall.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
  | delcall =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have htgt := (genericCall.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
  | statcall =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vgas hgas
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vtgt htgt
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vii hii
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vis his
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ voi hoi
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vos hos
      have hgc : ∀ a : Adr,
          (addAccessedAddress vos.2 vtgt.1).getCode a = devm.getCode a := by
        intro a
        rw [addAccessedAddress_getCode, Devm.popToNat_getCode hos,
          Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
          Devm.popToNat_getCode hii, Devm.popToAdr_getCode htgt,
          Devm.pop_getCode hgas]
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
            Except.pure] at hs
          repeat' split at hs
          all_goals
            simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
          all_goals obtain ⟨rfl, rfl⟩ := hs
          all_goals
            refine congrArg some (accessDelegation_codeAddress_of_none ?_)
            rw [hgc]
            exact hnodel

/-- Where a spawned child's code comes from.  Create frames enter fresh code at
an address that had none; `CALLCODE`/`DELEGATECALL` keep the parent's target;
the remaining call kinds load the callee's own code unless it delegates. -/
lemma Xinst.step_spawn_source {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm) :
    devm.getCode f.inner.currentTarget = .empty ∨
    f.inner.currentTarget = sevm.currentTarget ∨
    ( ¬ isValidDelegation (devm.getCode f.inner.currentTarget) →
        f.inner.code = devm.getCode f.inner.currentTarget ) := by
  rcases Xinst.step_shape sevm devm x with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, hf₀, -, hsrc, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · obtain ⟨-, htgt, hempty⟩ := genericCreate.step_spawn_frame hs
    exact Or.inl (by rw [htgt, hf.getCode na]; exact hempty)
  · obtain ⟨-, htgt, hcode⟩ := genericCall.step_spawn_frame hs
    rcases hsrc with rfl | hsrc
    · exact Or.inr (Or.inl htgt)
    · refine Or.inr (Or.inr fun hnd => ?_)
      rw [htgt] at hnd ⊢
      rw [hf₀.getCode t] at hnd ⊢
      rw [hcode]
      exact hsrc hnd

/-- Everything the child slot has to know about its own program location. -/
lemma Evm.step_spawn_child {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (he : f.enter = .run cevm) :
    cevm.pc = 0 ∧
    (∀ a : Adr, cevm.dyna.getCode a = devm.getCode a) ∧
    ( sevm.currentTarget ≠ cevm.sta.currentTarget →
      devm.getCode cevm.sta.currentTarget ≠ .empty →
      ¬ isValidDelegation (devm.getCode cevm.sta.currentTarget) →
      cevm.sta.code = devm.getCode cevm.sta.currentTarget ) := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hs
  have htgt := Frame.enter_run_currentTarget he
  have hcode := Frame.enter_run_code he
  refine ⟨Frame.enter_run_pc he, fun a => ?_, fun hne hnotEmpty hnotDel => ?_⟩
  · rw [Frame.enter_run_getCode he a]
    exact Xinst.step_spawn_getCode hx a
  · rw [htgt] at hne hnotEmpty hnotDel ⊢
    rw [hcode]
    rcases Xinst.step_spawn_source hx with hempty | hsame | hsrc
    · exact absurd hempty hnotEmpty
    · exact absurd hsame.symm hne
    · exact hsrc hnotDel

lemma chargeGas_getCode_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_error h).getCode a |>.symm

lemma Devm.push_getCode_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToAdr_getCode_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_error (core := Mach.popToAdr) h).getCode a |>.symm

lemma Rinst.preserves_getCode_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getCode_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => fun a => (s.get a).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (Devm.InstructionFrame.getCode hf a).symm

lemma Rinst.preserves_getCode_gen
    {pc sevm devm r exn}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = exn) (a : Adr)
    (_ne : (devm.getCode a).toList ≠ []) :
    Execution.getCode exn a = devm.getCode a := by
  cases exn <;> first | exact Rinst.preserves_getCode_err run a | exact Rinst.preserves_getCode run a

lemma Jinst.preserves_getCode
    {pc sevm devm j pc' devm'}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (hf.getCode a).symm

def JumpResult.getCode (ex : Except (EvmError × Devm) (Nat × Devm)) (a : Adr) : ByteArray :=
  match ex with
  | .ok ⟨_, devm⟩ => devm.getCode a
  | .error ⟨_, devm⟩ => devm.getCode a

lemma Jinst.preserves_getCode_gen
    {pc sevm devm j ex}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j ex) :
    ∀ a : Adr, JumpResult.getCode ex a = devm.getCode a := by
  intro a
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  cases ex <;> exact (hf.getCode a).symm

lemma Linst.dest_preserves_getCode {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Linst.Run sevm devm .dest exn) :
    ∀ adr : Adr, Execution.getCode exn adr = devm.getCode adr := by
  intro adr
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : devm.popToAdr <;> dsimp
  case error err =>
    intro run; rw [← run]; exact (Devm.popToAdr_getCode_err h1 adr)
  case ok res1 =>
    have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode adr = res1.2.getCode adr := by
      split
      · exact addAccessedAddress_getCode
      · rfl
    cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err =>
      intro run; rw [← run]
      change err.2.getCode adr = devm.getCode adr
      exact (chargeGas_getCode_err h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
    case ok res2 =>
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run; rw [← run]
        dsimp [assertDynamic, Except.assert] at h3
        split at h3
        · contradiction
        · simp only [Except.error.injEq] at h3; subst h3
          change res2.getCode adr = devm.getCode adr
          exact (chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run; rw [← run]
          change res2.getCode adr = devm.getCode adr
          exact (chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
        case some res3 =>
          have h_sub : res3.getCode adr = res2.getCode adr := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none =>
              rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              change st.getCode adr = res2.getCode adr
              exact State.subBal_getCode h_st
          by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos]
            intro run; rw [← run]
            change (addAccountToDelete _ _).getCode adr = devm.getCode adr
            have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
              dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
            have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode adr = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr := by
              dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
            have h_del : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode adr = ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode adr := by
              rfl
            exact h_del.trans (h_set.trans (h_add.trans (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))))
          · simp only [h_if]
            intro run; rw [← run]
            change (res3.addBal _ _).getCode adr = devm.getCode adr
            have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
              dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
            exact h_add.trans (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))

/-- Pointwise equality of code maps: the frame every non-create step keeps. -/
def Devm.CodeFrame (before after : Devm) : Prop :=
  ∀ a : Adr, after.getCode a = before.getCode a

theorem Linst.run_codeFrame {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution} (run : Linst.Run sevm devm l exn) :
    Execution.Rel Devm.CodeFrame devm exn := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · cases exn <;> exact Linst.dest_preserves_getCode run
  · have hf := Linst.run_instructionFrame sevm devm l h_not_dest
    rw [run] at hf
    cases exn <;> exact fun a => (hf.getCode a).symm

/-- Relational invariant carried by a filled recursive execution slot. -/
def Xlot.Rel (R : Devm → Devm → Prop) : Xlot → Prop
  | .none => True
  | .some ⟨evm, out⟩ => Execution.Rel R evm.dyna out

/-- Canonical outcome-aware effect of a regular instruction. -/
def Rinst.Effect (R : Devm → Devm → Prop) (r : Rinst) : Prop :=
  ∀ {pc sevm pre out},
    Rinst.run ⟨pc, sevm, pre⟩ r = out → Execution.Rel R pre out

/-- Canonical outcome-aware effect of a jump instruction. -/
def Jinst.Effect (R : Devm → Devm → Prop) (j : Jinst) : Prop :=
  ∀ {evm out},
    Jinst.Run evm j out →
      Outcome.Rel Prod.snd Prod.snd R evm.dyna out

/-- Canonical outcome-aware effect of a terminal instruction. -/
def Linst.Effect (R : Devm → Devm → Prop) (l : Linst) : Prop :=
  ∀ {sevm pre out},
    Linst.Run sevm pre l out → Execution.Rel R pre out

/-- Recursive-execution effect, parameterized by the relation on its child slot. -/
def Xinst.EffectRec (R : Devm → Devm → Prop) (x : Xinst) : Prop :=
  ∀ {sevm pre xl out},
    Xlot.Rel R xl → Xinst.Run sevm pre x xl out → Execution.Rel R pre out

/-- Nonterminal effect consumed by the mutual `Exec.effect` traversal. -/
def Ninst.EffectRec (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {pc sevm pre xl out},
    Xlot.Rel R xl → Ninst.StepRun pc sevm pre n xl out → Execution.Rel R pre out

/-- Successful-run relational projection used by `Func.effect`. -/
def Ninst.Effect (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {sevm pre post}, Ninst.Run sevm pre n post → R pre post

lemma Ninst.effectRec_reg {R : Devm → Devm → Prop} {r : Rinst}
    (hr : Rinst.Effect R r) : Ninst.EffectRec R (.reg r) := by
  intro pc sevm pre xl out hxl hrun
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
  obtain ⟨-, rfl⟩ := hrun
  exact hr rfl

lemma Ninst.effectRec_exec {R : Devm → Devm → Prop} {x : Xinst}
    (hx : Xinst.EffectRec R x) : Ninst.EffectRec R (.exec x) := by
  intro pc sevm pre xl out hxl hrun
  simp only [Ninst.StepRun, Ninst.step_exec] at hrun
  exact hx hxl (XStep.run_toStep.mp hrun)

/-- One step of the driver, related through whichever instruction the program
counter decodes to.  With the interpreter flattened this is the single place
where the four decode branches are enumerated; `Exec.effect` below then only
has to compose steps. -/
lemma Evm.step_effect {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel R xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel R devm out := by
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact hrefl _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      exact hn n hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := hj j (evm := ⟨pc, sevm, devm⟩) (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;>
        exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact hl l rfl

/-- The load-bearing traversal: per-instruction canonical effects compose into
`Execution.Rel` for a complete `Exec` derivation.  Where the old proof had one
case per mutual-block constructor, it now has one per driver outcome. -/
theorem Exec.effect {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  induction run with
  | halt hstep =>
    exact Evm.step_effect hrefl hn hj hl (xl := .none) trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | cont hstep _ ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .none) (out := .ok _) trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | doneErr hstep henter hr =>
    exact Evm.step_effect hrefl hn hj hl (xl := .none) trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | doneOk hstep henter hr _ ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .none) (out := .ok _) trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | runErr hstep henter _ hr ihc =>
    exact Evm.step_effect hrefl hn hj hl (xl := .some ⟨_, _⟩) ihc
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
  | runOk hstep henter _ hr _ ihc ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .some ⟨_, _⟩) (out := .ok _) ihc
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)

lemma Xlot.rel_of_filled {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {xl : Xlot} (hfilled : xl.Filled) : Xlot.Rel R xl := by
  cases xl with
  | none => trivial
  | some slot =>
    rcases slot with ⟨evm, out⟩
    rcases hfilled with ⟨hrun⟩
    exact Exec.effect hrefl htrans hn hj hl hrun

lemma Ninst.effect_of_effectRec {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l) :
    ∀ n, Ninst.Effect R n := by
  intro n sevm pre post hrun
  rcases hrun with ⟨xl, hfilled, pc, hrun'⟩
  have hrel := Xlot.rel_of_filled hrefl htrans hn hj hl hfilled
  exact hn n hrel hrun'

theorem Func.effect {R : Devm → Devm → Prop}
    (htrans : TransitiveRel R)
    (hpop : ∀ xs pre post, Devm.PopBurn xs pre post → R pre post)
    (hburn : ∀ pre post, Devm.Burn pre post → R pre post)
    (hn : ∀ n, Ninst.Effect R n)
    (hl : ∀ l, Linst.Effect R l)
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : R pre post := by
  induction run with
  | zero pop run' ih =>
    exact htrans (hpop _ _ _ pop) ih
  | succ neq pop burn run' ih =>
    exact htrans (hpop _ _ _ pop) (htrans (hburn _ _ burn) ih)
  | last run' =>
    exact hl _ run'
  | next runi run' ih =>
    exact htrans (hn _ runi) ih
  | call eq burn run' ih =>
    exact htrans (hburn _ _ burn) ih

-- Relational form of code preservation: nonempty code is never modified.
def Devm.CodePreserve (pre post : Devm) : Prop :=
  ∀ a : Adr, (pre.getCode a).toList ≠ [] → post.getCode a = pre.getCode a

lemma codePreserve_refl_trans :
    ReflexiveRel Devm.CodePreserve ∧ TransitiveRel Devm.CodePreserve := by
  constructor
  · intro d a _; rfl
  · intro a b c hab hbc adr ha
    have h1 := hab adr ha
    have h2 : (b.getCode adr).toList ≠ [] := by rw [h1]; exact ha
    exact (hbc adr h2).trans h1

lemma Xlot.invGetCode_of_rel {xl : Xlot}
    (h : Xlot.Rel Devm.CodePreserve xl) : xl.InvGetCode := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · intro a ha
    cases exn with
    | error e => exact (h a ha).symm
    | ok d => exact (h a ha).symm

/-- Reverse bridge: the observation invariant `InvGetCode` implies the
relational `Xlot.Rel Devm.CodePreserve`.  Together with
`Xlot.invGetCode_of_rel` this makes the two forms interchangeable, so the
legacy `Xinst.preserves_getCode_gen` can project through the relational master. -/
lemma Xlot.rel_of_invGetCode {xl : Xlot}
    (h : xl.InvGetCode) : Xlot.Rel Devm.CodePreserve xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · cases exn with
    | error e => exact fun a ha => (h a ha).symm
    | ok d => exact fun a ha => (h a ha).symm

lemma Rinst.codePreserve_effect (r : Rinst) :
    Rinst.Effect Devm.CodePreserve r := by
  intro pc sevm pre out hrun
  have h := Rinst.preserves_getCode_gen hrun
  cases out <;> exact fun a ha => h a ha

/-- Canonical relational code-preservation master for `Xinst`.  This carries the
full per-constructor case analysis, composing the world-silent primitive frames
(pops, gas, memory, access bookkeeping) with the Step 7.3 generic-operation
masters `GenericCall.codePreserve` / `GenericCreate.codePreserve`.  The legacy
observation theorem `Xinst.preserves_getCode_gen` is a projection of this master via
the `Xlot.InvGetCode` / `Xlot.Rel Devm.CodePreserve` bridge. -/
lemma Xinst.codePreserve_effectRec (x : Xinst) :
    Xinst.EffectRec Devm.CodePreserve x := by
  intro sevm devm xl exn hxl run
  have inv : xl.InvGetCode := Xlot.invGetCode_of_rel hxl
  have lift : ∀ {d : Devm}, Devm.InstructionFrame devm d →
      Execution.CodePreserve d exn →
      Execution.Rel Devm.CodePreserve devm exn := by
    intro d hf h
    have key : ∀ a : Adr, (devm.getCode a).toList ≠ [] →
        Execution.getCode exn a = devm.getCode a := by
      intro a ha
      rw [hf.getCode a] at ha ⊢
      exact h a ha
    cases exn with
    | error e => exact fun a ha => key a ha
    | ok d' => exact fun a ha => key a ha
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm devm x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;>
    rw [hs] at run
  -- the whole step stayed inside the instruction frame
  · obtain ⟨-, rfl⟩ := run
    exact Outcome.Rel.mono (fun _ _ hfr a _ => (hfr.getCode a).symm) hframe
  -- dispatched to the CREATE family
  · exact lift hf (GenericCreate.codePreserve inv run)
  -- dispatched to the CALL family
  · exact lift hf (GenericCall.codePreserve inv run)

/-- Compatibility projection: the legacy observation theorem, now derived from
the relational master `Xinst.codePreserve_effectRec` through the
`Xlot.rel_of_invGetCode` bridge.  Statement unchanged. -/
lemma Xinst.preserves_getCode_gen
    {sevm devm x xl exn}
    (inv : xl.InvGetCode)
    (run : Xinst.Run sevm devm x xl exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a := by
  have h := Xinst.codePreserve_effectRec x (Xlot.rel_of_invGetCode inv) run
  cases exn with
  | error e => exact fun a ha => h a ha
  | ok d => exact fun a ha => h a ha

lemma Ninst.push_instructionFrame_effectRec
    {xs : Bytes} {hxs : xs.length ≤ 32} :
    Ninst.EffectRec Devm.InstructionFrame (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hRun
  obtain ⟨-, rfl⟩ := hRun
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (if xs = [] then gBase else gVerylow) pre)
  exact Devm.push_instructionFrame xs.toB256

lemma Ninst.push_effectRec_of_instructionFrame
    {R : Devm → Devm → Prop} {xs : Bytes} {hxs : xs.length ≤ 32}
    (hIR : ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → R d d') :
    Ninst.EffectRec R (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  have h0 : xl = .none := by
    simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hRun
    exact hRun.1
  subst h0
  exact Outcome.Rel.mono hIR
    (Ninst.push_instructionFrame_effectRec (hxs := hxs) (xl := .none)
      trivial hRun)

lemma Ninst.push_codePreserve_effectRec {xs : Bytes} {hxs : xs.length ≤ 32} :
  Ninst.EffectRec Devm.CodePreserve (.push xs hxs) := by
  exact Ninst.push_effectRec_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Ninst.codePreserve_effectRec (n : Ninst) :
    Ninst.EffectRec Devm.CodePreserve n := by
  cases n with
  | reg r =>
    exact Ninst.effectRec_reg (Rinst.codePreserve_effect r)
  | exec x =>
    exact Ninst.effectRec_exec (Xinst.codePreserve_effectRec x)
  | push xs hxs =>
    exact Ninst.push_codePreserve_effectRec

lemma Jinst.codePreserve_effect (j : Jinst) :
    Jinst.Effect Devm.CodePreserve j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact fun a _ => (hf.getCode a).symm

lemma Linst.codePreserve_effect (l : Linst) :
    Linst.Effect Devm.CodePreserve l := by
  intro sevm pre out hrun
  have hf := Linst.run_codeFrame hrun
  cases out <;> exact fun a _ => hf a

lemma Exec.preserves_getCode {pc} {sevm} {devm} {exn}
    (run : Exec pc sevm devm exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a := by
  intro a ha
  have h := Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect
    Linst.codePreserve_effect run
  cases exn with
  | error e => exact h a ha
  | ok d => exact h a ha

lemma not_empty_of_compile {p : Prog} {code : ByteArray} (h : some code.toList = Prog.compile p) : code ≠ .empty := by
  intro hc
  have h_ne : Prog.compile p ≠ some [] := Prog.compile_ne_nil
  rw [←h, hc] at h_ne
  have h_empty_toList : ByteArray.empty.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    rfl
  rw [h_empty_toList] at h_ne
  exact h_ne rfl

lemma not_delegation_of_compile {p : Prog} {code : ByteArray}
    (h : some code.toList = Prog.compile p) : ¬ isValidDelegation code := by
  unfold isValidDelegation
  unfold Prog.compile at h
  unfold table at h
  simp only [Table.compile] at h
  simp only [bind] at h
  symm at h
  rcases of_bind_eq_some h with ⟨bs, h_bs, h'⟩
  rcases of_bind_eq_some h' with ⟨bss, h_bss, h_eq⟩
  injection h_eq with h_eq
  intro h_del
  rcases h_del with ⟨h_size, h_slice⟩
  have h_slice_eq : code.sliceD 0 3 0 = code.toList.sliceD 0 3 0 := ByteArray.sliceD_eq _ _ _ _
  rw [h_slice_eq, ←h_eq, eoaDelegationMarker] at h_slice
  revert h_slice
  simp only [List.sliceD]
  intro h_false
  injection h_false with h_false
  change (91 : UInt8) = 239 at h_false
  contradiction

/-- The "we are inside the contract" case, shared by every driver outcome:
either the run failed (nothing to prove) or it completed a program run at
`pc = 0`, which the depth induction turns into the contract-level invariant. -/
private lemma lift_core.atTarget
    {ε : Nat → Sevm → Devm → Execution → Prop} {π : Sevm → Devm → Devm → Prop}
    {ca : Adr} {p : Prog}
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca → ε pc sevm devm (.error ⟨err, devm'⟩) )
    {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (ex : Exec pc sevm devm exn)
    (h_fa : ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e))
    (h_at_p : p.At ca pc sevm devm) (h_eq : sevm.currentTarget = ca) :
    ε pc sevm devm exn := by
  cases exn with
  | error e => exact errAtTarget h_eq
  | ok post =>
    have h_pc : pc = 0 := (h_at_p.right h_eq).right
    subst h_pc
    exact analog
      (depth_ind (correct sevm devm p post ex (h_at_p.right h_eq).left) h_eq h_fa)

/-- Code preservation across one driver step, in the form the `Prog.At`
bookkeeping needs. -/
lemma lift_core.stepCode {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {xl : Xlot} (hxl : Xlot.Rel Devm.CodePreserve xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl (.ok devm'))
    (a : Adr) (ha : (devm.getCode a).toList ≠ []) :
    devm'.getCode a = devm.getCode a :=
  Evm.step_effect codePreserve_refl_trans.1 Ninst.codePreserve_effectRec
    Jinst.codePreserve_effect Linst.codePreserve_effect hxl hrun a ha

/-- The eliminator every contract-level invariant proof runs on: strong
induction on frame depth combined with the driver's case analysis, carrying the
program-location bookkeeping (`Prog.At`) across steps and across suspensions.
Its handlers stay indexed by *instruction kind*, so the decode dispatch happens
here once and `lift`/`lift_inv` are insulated from the flattening. -/
lemma lift_core
    (ε : Nat → Sevm → Devm → Execution → Prop)
    (π : Sevm → Devm → Devm → Prop)
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    (ca : Adr) (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( invOp :
      ∀ {pc sevm devm},
        sevm.code.getInst pc = none →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨.halt (.invalidOpcode .none), devm⟩) )
    ( nextNoneErr :
      ∀ {pc sevm devm n err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextSomeErr :
      ∀ {pc sevm devm n evm_ exn_ err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.error ⟨err, devm'⟩) →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextNoneRec :
      ∀ {pc sevm devm n devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.ok devm') →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( nextSomeRec :
      ∀ {pc sevm devm n evm_ exn_ devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.ok devm') →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( jumpErr :
      ∀ {pc sevm devm j err devm'},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( jumpRec :
      ∀ {pc sevm devm j pc' devm' exn},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩) →
        Exec pc' sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε pc' sevm devm' exn →
        ε pc sevm devm exn )
    ( last :
      ∀ {pc sevm devm l exn},
        Linst.At sevm.code pc l →
        Linst.Run sevm devm l exn →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm exn ) :
    Exec.Fa (Exec.Wkn ca p (fun pc s d e _ => ε pc s d e)) := by
  apply Exec.strong_rec
  apply @Exec.rec (Fortify (Exec.Wkn ca p (fun pc s d e _ => ε pc s d e)))
  -- halt
  · intro pc sevm devm ex hstep h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.halt hstep) h_fa h_at_p h_eq
    · rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
      · rw [Evm.step_invOp hgi] at hstep
        cases hstep
        exact invOp hgi h_ne
      · cases i with
        | next n =>
          have hns : Ninst.step ⟨pc, sevm, devm⟩ n = .halt ex := by
            rw [← Evm.step_next (n := n) hgi]; exact hstep
          have hrun : Ninst.StepRun pc sevm devm n .none ex := by
            unfold Ninst.StepRun; rw [hns]; exact ⟨rfl, rfl⟩
          cases ex with
          | error e => exact nextNoneErr hgi hrun h_ne
          | ok d => exact absurd hns Ninst.step_ne_halt_ok
        | jump j =>
          rw [Evm.step_jump (j := j) hgi] at hstep
          rcases hj : j.run ⟨pc, sevm, devm⟩ with e | ⟨pc', devm'⟩ <;>
            rw [hj] at hstep <;> simp only [Step.ofJump] at hstep
          · cases hstep; exact jumpErr hgi hj h_ne
          · cases hstep
        | last l =>
          rw [Evm.step_last (l := l) hgi] at hstep
          cases hstep
          exact last hgi rfl h_ne
  -- cont
  · intro pc sevm devm pc' devm' exn hstep ex ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.cont hstep ex) h_fa h_at_p h_eq
    · have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core.stepCode (xl := .none) trivial
          (by rw [hstep]; exact ⟨rfl, rfl⟩) ca h_ne_code
      have h_at' : p.At ca pc' sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
      · rw [Evm.step_invOp hgi] at hstep; cases hstep
      · cases i with
        | next n =>
          have hns : Ninst.step ⟨pc, sevm, devm⟩ n = .cont pc' devm' := by
            rw [← Evm.step_next (n := n) hgi]; exact hstep
          have hpc : pc' = pc + n.size := Ninst.step_cont_pc hns
          subst hpc
          have hrun : Ninst.StepRun pc sevm devm n .none (.ok devm') := by
            unfold Ninst.StepRun; rw [hns]; exact ⟨rfl, rfl⟩
          exact nextNoneRec hgi hrun ex h_ne (ih h_fa h_at')
        | jump j =>
          rw [Evm.step_jump (j := j) hgi] at hstep
          exact jumpRec hgi (Step.ofJump_cont hstep) ex h_ne (ih h_fa h_at')
        | last l =>
          rw [Evm.step_last (l := l) hgi] at hstep; cases hstep
  -- doneErr
  · intro pc sevm devm f rsm pc' r e hstep henter hr h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.doneErr hstep henter hr) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, -⟩ := Evm.step_spawn_inv hstep
      have hrun : Ninst.StepRun pc sevm devm (.exec x) .none (.error e) := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨r, RunFrame.of_done henter, hr.symm⟩
      exact nextNoneErr hxat hrun h_ne
  -- doneOk
  · intro pc sevm devm f rsm pc' r devm' exn hstep henter hr ex ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.doneOk hstep henter hr ex) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
      subst hpc'
      have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have hrun : Ninst.StepRun pc sevm devm (.exec x) .none (.ok devm') := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨r, RunFrame.of_done henter, hr.symm⟩
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core.stepCode (xl := .none) trivial
          (by rw [hstep]; exact ⟨r, RunFrame.of_done henter, hr.symm⟩) ca h_ne_code
      have h_at' : p.At ca (pc + 1) sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      exact nextNoneRec hxat hrun ex h_ne (ih h_fa h_at')
  -- runErr
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter child hr ihc h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.runErr hstep henter child hr) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, -⟩ := Evm.step_spawn_inv hstep
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hdepth : cevm.sta.depth < sevm.depth := by
        rw [Frame.enter_run_depth henter]; exact Step.spawn_depth_lt hstep
      have h_at_child : p.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [hgc ca]; exact h_at_p.left, fun hct => ⟨?_, hpc0⟩⟩
        have hne' : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [hct]; exact h_ne
        have hcode := hsrc hne'
          (by rw [hct]; exact not_empty_of_compile h_at_p.left)
          (by rw [hct]; exact not_delegation_of_compile h_at_p.left)
        rw [hcode, hct]
        exact h_at_p.left
      have hrun :
          Ninst.StepRun pc sevm devm (.exec x) (.some ⟨cevm, raw⟩) (.error e) := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩
      exact nextSomeErr hxat hrun child h_ne
        (h_fa cevm.pc cevm.sta cevm.dyna raw child hdepth h_at_child)
  -- runOk
  · intro pc sevm devm f rsm pc' cevm raw devm' exn hstep henter child hr ex
      ihc ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.runOk hstep henter child hr ex) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
      subst hpc'
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hdepth : cevm.sta.depth < sevm.depth := by
        rw [Frame.enter_run_depth henter]; exact Step.spawn_depth_lt hstep
      have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have h_at_child : p.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [hgc ca]; exact h_at_p.left, fun hct => ⟨?_, hpc0⟩⟩
        have hne' : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [hct]; exact h_ne
        have hcode := hsrc hne'
          (by rw [hct]; exact not_empty_of_compile h_at_p.left)
          (by rw [hct]; exact not_delegation_of_compile h_at_p.left)
        rw [hcode, hct]
        exact h_at_p.left
      have hchild : Xlot.Rel Devm.CodePreserve (.some ⟨cevm, raw⟩) :=
        Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
          Ninst.codePreserve_effectRec Jinst.codePreserve_effect
          Linst.codePreserve_effect child
      have hrun :
          Ninst.StepRun pc sevm devm (.exec x) (.some ⟨cevm, raw⟩) (.ok devm') := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core.stepCode (xl := .some ⟨cevm, raw⟩) hchild
          (by rw [hstep]; exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩)
          ca h_ne_code
      have h_at' : p.At ca (pc + 1) sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      exact nextSomeRec hxat hrun child ex h_ne
        (h_fa cevm.pc cevm.sta cevm.dyna raw child hdepth h_at_child)
        (ih h_fa h_at')

lemma lift
    (R : Sevm → Devm → Devm → Prop)
    (ca : Adr) -- contract address
    (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallSubExec sevm.depth ca p R →
        R sevm pre post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'}
        {exn' : Execution} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n
          (.some ⟨evm', exn'⟩)
          (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        ifOk (R evm'.sta evm'.dyna) exn' →
        R sevm inter post →
        R sevm pre post )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter} {post},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        Exec pc' sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm pre post ) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      Prog.At p ca pc sevm pre →
      R sevm pre post := by
  intro pc sevm pre post h_exc h_at
  refine lift_core (fun _ sevm pre exn => ifOk (R sevm pre) exn) R (fun h => h) ca p
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pc sevm pre (.ok post) h_exc h_at
  · intro sevm' pre' post' h_run h_eq h_fa
    apply depth_ind h_run h_eq
    intro pc_ sevm_ devm_ post_ h_exc' h_lt h_at'
    exact h_fa pc_ sevm_ devm_ (.ok post_) h_exc' h_lt h_at'
  · intro pc' sevm' devm' err devm'' h_eq; exact trivial
  · intro pc' sevm' devm' h_get h_ne; exact trivial
  · intro pc' sevm' devm' n err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' n evm_ exn_ err devm'' h_at' h_run ex_sub h_ne h_ih; exact trivial
  · intro pc' sevm' devm' n devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextNone h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' n evm_ exn_ devm'' exn h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextSome h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
  · intro pc' sevm' devm' j err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' j pc_ devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact jump h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' l exn h_at' h_run h_ne
    cases exn with
    | error e => exact trivial
    | ok post' => exact last h_at' h_run h_ne

lemma lift_inv
    (ca : Adr) (p : Prog)
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( with_depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            Prog.At p ca pc' sevm' pre' →
            σ sevm' pre' →
            ρ sevm' post' ) →
        σ sevm pre →
        ρ sevm post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'} {exn'} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n (.some ⟨evm', exn'⟩) (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ evm'.sta evm'.dyna ∧ (ifOk (ρ evm'.sta) exn' → σ sevm inter) )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        ρ sevm post ) :
    ∀ pc sevm devm post,
      Exec pc sevm devm (.ok post) →
      Prog.At p ca pc sevm devm →
      σ sevm devm →
      ρ sevm post := by
  apply @Blanc.lift (fun sevm pre post => σ sevm pre → ρ sevm post) ca p with_depth_ind
  · intro pc sevm pre n inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (nextNone h_at h_run h_ne h_pi)
  · intro pc sevm pre n evm' exn' inter post h_at h_run ex_sub _ h_ne h_ifOk h_ih h_pi
    rcases nextSome h_at h_run ex_sub h_ne h_pi with ⟨h_pi_sub, h_imp⟩
    apply h_ih; apply h_imp
    cases exn' with
    | error e => exact trivial
    | ok post' => exact h_ifOk h_pi_sub
  · intro pc sevm pre j pc' inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (jump h_at h_run h_ne h_pi)
  · intro pc sevm pre l post h_at h_run h_ne h_pi
    exact last h_at h_run h_ne h_pi

syntax "show_prefix_zero" : tactic
macro_rules
  | `(tactic| show_prefix_zero) =>
    `(tactic| intros h0 h1; apply append_pref h0.stack h1)

syntax "show_prefix_one" : tactic
macro_rules
  | `(tactic| show_prefix_one) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases List.of_cons_pref_of_cons_pref h1 (pref_of_split h2) with ⟨hx, h⟩;
              cases hx; clear h; apply append_pref h3 (of_append_pref h2 h1) )

syntax "show_prefix_two" : tactic
macro_rules
  | `(tactic| show_prefix_two) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', y', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩;
              cases hx; cases hy; clear h; apply append_pref h3 (of_append_pref h2 h1) )


infix:70 " <? "  => B256.ltCheck
infix:70 " >? "  => B256.gtCheck
infix:70 " ±<? " => B256.sltCheck
infix:70 " ±>? " => B256.sgtCheck
infix:70 " =? "  => B256.eqCheck

lemma Bytes.sig_zero_cons (xs) : Bytes.sig (0 :: xs) = Bytes.sig xs := rfl
lemma Bytes.sig_nonzero_cons (x xs) (h : x ≠ 0) : Bytes.sig (x :: xs) = x :: xs := by
  simp only [Jaune.Bytes.sig]; rw [List.dropWhile_cons_of_neg]; simp [h]

lemma Bytes.toB256_sig (bs : Bytes) : Bytes.toB256 (Bytes.sig bs) = bs.toB256 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : b = 0
    · cases h; rw [sig_zero_cons, ih, Bytes.toB256_zero_cons]
    · rw [sig_nonzero_cons b bs h]

def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop :=
  ∃ s' : Stack, Stack.Pop xs s s' ∧ Stack.Push zs s' s''

def Stack.SwapCore (x y : B256) : Nat → Stack → Stack → Prop
  | 0, y' :: xs, x' :: xs' => x = x' ∧ y = y' ∧ xs = xs'
  | n + 1, z :: xs, z' :: xs' => z = z' ∧ SwapCore x y n xs xs'
  | _, _, _ => False

def Stack.Swap (n : Nat) : Stack → Stack → Prop
  | x :: xs, y :: xs' => SwapCore x y n xs xs'
  | _, _ => False

def Devm.Push (xs : List B256) : Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Push xs}

def Devm.DiffBurn (xs ys : List B256) : Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Diff xs ys, gasLeft := (· ≥ ·)}

lemma Devm.push_of_push {x : B256} {s s' : Devm} (h : Devm.push x s = .ok s') :
    Devm.Push [x] s s' := by
  rw [Devm.push_def] at h
  simp only [Except.assert, bind, Except.bind] at h
  split at h
  · cases h
  · injection h with eq; subst eq
    constructor <;>
      simp [Devm.Rels.eq, Stack.Push, Split, Devm.setMach]
    all_goals rfl

lemma Devm.pushBurn_of_burn_of_push {xs : List B256} {s s' s'' : Devm}
    (burn : Devm.Burn s s') (push : Devm.Push xs s' s'') :
    Devm.PushBurn xs s s'' := by
  constructor
  · exact burn.stack ▸ push.stack
  · exact Eq.trans burn.memory push.memory
  · rw [← push.gasLeft]; exact burn.gasLeft
  · exact Eq.trans burn.logs push.logs
  · exact Eq.trans burn.refundCounter push.refundCounter
  · exact Eq.trans burn.output push.output
  · exact Eq.trans burn.accountsToDelete push.accountsToDelete
  · exact Eq.trans burn.returnData push.returnData
  · exact Eq.trans burn.error push.error
  · exact Eq.trans burn.accessedAddresses push.accessedAddresses
  · exact Eq.trans burn.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans burn.state push.state
  · exact Eq.trans burn.createdAccounts push.createdAccounts
  · exact Eq.trans burn.transientStorage push.transientStorage

lemma Devm.diffBurn_of_pop_of_pushBurn {xs ys : List B256} {s s' s'' : Devm}
    (pop : Devm.Pop xs s s') (push : Devm.PushBurn ys s' s'') :
    Devm.DiffBurn xs ys s s'' := by
  constructor
  · exact ⟨s'.stack, pop.stack, push.stack⟩
  · exact Eq.trans pop.memory push.memory
  · rw [pop.gasLeft]; exact push.gasLeft
  · exact Eq.trans pop.logs push.logs
  · exact Eq.trans pop.refundCounter push.refundCounter
  · exact Eq.trans pop.output push.output
  · exact Eq.trans pop.accountsToDelete push.accountsToDelete
  · exact Eq.trans pop.returnData push.returnData
  · exact Eq.trans pop.error push.error
  · exact Eq.trans pop.accessedAddresses push.accessedAddresses
  · exact Eq.trans pop.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans pop.state push.state
  · exact Eq.trans pop.createdAccounts push.createdAccounts
  · exact Eq.trans pop.transientStorage push.transientStorage

lemma Devm.pushBurn_of_pushItem {v : B256} {cost : Nat} {s s' : Devm}
    (h : pushItem v cost s = .ok s') : Devm.PushBurn [v] s s' := by
  rw [pushItem_def] at h; exact Devm.pushBurn_of_run h

lemma Devm.diffBurn_of_applyUnary {f : B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyUnary f cost s = .ok s') :
    ∃ x, Devm.DiffBurn [x] [f x] s s' := by
  rw [applyUnary_def] at h
  rcases Except.bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h2⟩
  simp only at h2
  rw [pushItem_def] at h2
  refine ⟨x, Devm.diffBurn_of_pop_of_pushBurn (Devm.pop_of_pop h1) (Devm.pushBurn_of_run h2)⟩

lemma Devm.diffBurn_of_applyBinary {f : B256 → B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyBinary f cost s = .ok s') :
    ∃ x y, Devm.DiffBurn [x, y] [f x y] s s' := by
  rw [applyBinary_def] at h
  rcases Except.bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h'⟩
  rcases Except.bind_eq_ok h' with ⟨⟨y, s₂⟩, h2, h3⟩
  simp only at h3
  rw [pushItem_def] at h3
  refine ⟨x, y, Devm.diffBurn_of_pop_of_pushBurn
    (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2))
    (Devm.pushBurn_of_run h3)⟩

lemma Devm.pop_of_popToNat {k : Nat} {devm devm' : Devm}
    (h : Devm.popToNat devm = .ok ⟨k, devm'⟩) :
    ∃ x, Devm.Pop [x] devm devm' := by
  rw [Devm.popToNat_def] at h
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩ <;> simp [hp] at h
  rcases h with ⟨_, rfl⟩
  exact ⟨x, Devm.pop_of_pop hp⟩

/-- `popToNat` pops a word and reports *that word's* `toNat`.

A third instance of the same projection `of_run_calldataload_val` restores:
`Devm.pop_of_popToNat` above proves `∃ x, Devm.Pop [x] devm devm'` and drops the
only interesting fact, namely that the `Nat` handed to the rest of the
instruction is `x.toNat`. Every memory-address and size operand in the machine
arrives through this function, so the value-carrying form is a prerequisite for
saying anything about *where* an instruction wrote or *how much*. -/
lemma Devm.pop_of_popToNat_val {k : Nat} {devm devm' : Devm}
    (h : Devm.popToNat devm = .ok ⟨k, devm'⟩) :
    ∃ x, Devm.Pop [x] devm devm' ∧ k = x.toNat := by
  rw [Devm.popToNat_def] at h
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩ <;> simp [hp] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨x, Devm.pop_of_pop hp, rfl⟩

lemma of_run_reg {e : Sevm} {s s' : Devm} {r : Rinst}
    (h : Ninst.Run e s (Ninst.reg r) s') :
    ∃ pc, Rinst.run ⟨pc, e, s⟩ r = .ok s' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact ⟨pc, run.2.symm⟩

/-- The atomic static fact: `SSTORE` clears `assertDynamic` before it commits,
so a successful storage write witnesses a dynamic context. -/
theorem of_run_sstore_not_static {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s sstore s') : e.isStatic = false := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨_, _⟩, _, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨_, _⟩, _, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨_, _⟩, _, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, _, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨_, _, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨_, _, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, hassert, _⟩
  unfold assertDynamic Except.assert at hassert
  split at hassert
  · rename_i hdynamic
    simpa using hdynamic
  · exact absurd hassert (by simp)

lemma of_run_push {e s s' xs p} (h : Ninst.Run e s (push xs p) s') :
    Devm.PushBurn [xs.toB256] s s' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at run
  exact Devm.pushBurn_of_run run.2.symm

/-- A successful `push` run, as the executable equation the `Hinv` instance
proofs consume.  This is where the driver's step-outcome shape is unwound, once,
for every push-shaped instance. -/
lemma Ninst.run_push_eq {e : Sevm} {s s' : Devm} {xs : Bytes} {le : xs.length ≤ 32}
    (h : Ninst.Run e s (.push xs le) s') :
    (do let d ← chargeGas (if xs = [] then gBase else gVerylow) s
        d.push xs.toB256) = .ok s' := by
  rcases h with ⟨xl, -, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at run
  exact run.2.symm

lemma of_run_pushB256 {e s s' x} (h : Ninst.Run e s (pushB256 x) s') :
    Devm.PushBurn [x] s s' := by
  have h' := of_run_push h
  rwa [Bytes.toB256_sig, B256.toB256_toBytes] at h'

lemma of_run_pop {e : Sevm} {s s' : Devm} (h : Ninst.Run e s pop s') :
    ∃ x, Devm.PopBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop s with _ | ⟨x, s₂⟩ <;> simp [hp] at h1
  subst h1
  exact ⟨x, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp) (Devm.burn_of_chargeGas h2)⟩

lemma of_run_dup {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (dup n) s') :
    ∃ x, s.stack[n.val]? = some x ∧ Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i x hx
    refine ⟨x, ?_, Devm.pushBurn_of_burn_of_push hb (Devm.push_of_push h2)⟩
    rw [hb.stack]; exact hx

lemma of_run_swap {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (swap n) s') :
    List.swap s.stack n.val = some s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i stk hstk
    injection h2 with eq; subst eq
    rw [hb.stack]; exact hstk

lemma of_run_caller {e : Sevm} {s s' : Devm} (h : Ninst.Run e s caller s') :
    Devm.PushBurn [e.caller.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_callvalue {e : Sevm} {s s' : Devm} (h : Ninst.Run e s callvalue s') :
    Devm.PushBurn [e.value] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- Value-carrying inversion for `CALLDATASIZE`. -/
lemma of_run_calldatasize {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s calldatasize s') :
    Devm.PushBurn [e.data.length.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- Value-carrying inversion for `CODESIZE`.  Constructor decoders compare the
complete creation-code image, not merely the compiled executable prefix. -/
lemma of_run_codesize {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s codesize s') :
    Devm.PushBurn [e.code.size.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_mstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  refine ⟨x, v, ?_⟩
  have hp := (Devm.pop_append p1 p2).stack
  rw [← eq]
  rw [show (Devm.memWrite s₃ i v.toBytes).stack = s₃.stack from rfl, ← hb.stack]
  exact hp

lemma Devm.pop_of_popN {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    l.length = n ∧ Devm.Pop l devm devm' := by
  induction n generalizing devm l with
  | zero =>
    rw [Devm.popN_def] at hp
    injection hp with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    refine ⟨rfl, ?_⟩
    constructor <;> simp [Devm.Rels.eq, Stack.Pop, Split]
  | succ n ih =>
    rw [Devm.popN_def] at hp
    rcases Except.bind_eq_ok hp with ⟨⟨x, devm1⟩, hp1, hp2⟩
    rcases Except.bind_eq_ok hp2 with ⟨⟨xs, devm2⟩, hp3, hp4⟩
    injection hp4 with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    rcases ih hp3 with ⟨h_len, h_pop⟩
    refine ⟨by simp [h_len], Devm.pop_append (Devm.pop_of_pop hp1) h_pop⟩

lemma of_run_sstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hp := (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2)).stack
  have hb := Devm.burn_of_chargeGas h7
  have h_s₃ : s₃.stack = s₂.stack := by
    injection h4 with eq
    split at eq <;> (injection eq with eq _; subst eq; rfl)
  have h_s₄ : s₄.stack = s₃.stack := by
    injection h6 with eq; rw [← eq]
    rfl
  injection h9 with eq
  refine ⟨x, y, ?_⟩
  rw [← eq]
  show Stack.Pop [x, y] s.stack s₅.stack
  rw [← hb.stack, h_s₄, h_s₃]
  exact hp

/-- `Devm.memWrite` changes memory to the requested write. -/
@[simp] lemma Devm.memWrite_memory (devm : Devm) (i : Nat) (val : Bytes) :
    (devm.memWrite i val).memory = devm.memory.write i val := rfl

/-- `Devm.memWrite` leaves the operand stack unchanged. -/
lemma Devm.memWrite_stack (devm : Devm) (i : Nat) (val : Bytes) :
    (devm.memWrite i val).stack = devm.stack := rfl

/-- `calldatacopy` writes *the calldata slice named by its operands* into memory.

The value-carrying form, and the piece (1b) of the arc needs: the bytes written
are `e.data.sliceD y.toNat z.toNat 0`, a function of `e.data` and the popped
operands alone. `d` is the state the instruction reaches after popping its three
operands and charging, so the equation says the whole effect on `d` is this one
write.

Two things this deliberately does *not* say, because Blanc has no vocabulary for
either yet (see the module note at `Sevm.dataWord`): that `d`'s memory agrees
with `s`'s, and what a subsequent `mload` of the written range yields. Both need
a `Mem.read`/`Mem.write` algebra that neither repository has. -/
lemma of_run_calldatacopy_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z d, Stack.Pop [x, y, z] s.stack (Devm.stack d) ∧
      s' = Devm.memWrite d x.toNat (e.data.sliceD y.toNat z.toNat 0) := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  refine ⟨x, y, z, s₄, ?_, eq.symm⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← hb.stack]
  exact hp

lemma of_run_calldatacopy {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack := by
  rcases of_run_calldatacopy_val h with ⟨x, y, z, d, hp, rfl⟩
  exact ⟨x, y, z, by rw [Devm.memWrite_stack]; exact hp⟩

lemma of_run_singleton {e s i s'} (h : Line.Run e s [i] s') : Ninst.Run e s i s' := by
  rcases Line.of_run_cons h with ⟨_, hrun, hnil⟩
  cases hnil; exact hrun

/-- `calldataload` pops an offset and pushes *the calldata word at it*.

The value-carrying form, and the point at which Blanc stops discarding what the
calldata says. `Rinst.runCore .calldataload` pushes
`Bytes.toB256 (e.data.sliceD start.toNat 32 0)`, which is `Sevm.dataWord e x` by
definition; the value-forgetting `of_run_calldataload` below is now literally
this statement with the pushed word quantified away, which is all a safety
invariant ever needed and all any existing consumer asks for.

Because `Sevm.dataWord` zero-pads (`List.sliceD`'s default), this holds for
calldata of every length — no well-formedness premise appears or is available. -/
lemma of_run_calldataload_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldataload s') :
    ∃ x, Stack.Diff [x] [Sevm.dataWord e x] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  have hpop := Devm.pop_of_pop h1
  have hb := Devm.burn_of_chargeGas h2
  have hpush : Devm.Push [Sevm.dataWord e si] s₂ s' := Devm.push_of_push run₂
  refine ⟨si, s₁.stack, hpop.stack, ?_⟩
  rw [show s₁.stack = s₂.stack from hb.stack]
  exact hpush.stack

/-- The value-forgetting form. Statement unchanged; its ~75 consumers across
`Solvent.lean` and `Conserved.lean` see exactly what they always did, and the
pop/charge/push destructuring is now done once, in the strong form above. -/
lemma of_run_calldataload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldataload s') :
    ∃ x y, Stack.Diff [x] [y] s.stack s'.stack := by
  rcases of_run_calldataload_val h with ⟨x, hd⟩
  exact ⟨x, _, hd⟩

lemma Devm.memRead_stack (devm : Devm) (i n : Nat) :
    (devm.memRead i n).2.stack = devm.stack := rfl

lemma of_run_kec {e : Sevm} {s s' : Devm} (h : Ninst.Run e s kec s') :
    ∃ x y z, Stack.Diff [x, y] [z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  have hb := Devm.burn_of_chargeGas h3
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] (s₃.memRead mi sz).2 s' :=
    ⟨_, Devm.push_of_push run₃⟩
  refine ⟨x, y, val, s₂.stack, (Devm.pop_append p1 p2).stack, ?_⟩
  rw [show s₂.stack = s₃.stack from hb.stack, ← Devm.memRead_stack s₃ mi sz]
  exact hpush.stack

lemma of_run_log {e : Sevm} {s s' : Devm} {n : Fin 5} (h : Ninst.Run e s (log n) s') :
    ∃ zs, zs.length = n.val + 2 ∧ Stack.Pop zs s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨h_len, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases h_mem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_s₅ : s₅.stack = s₄.stack := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]; rfl
  refine ⟨x :: y :: topics, by simp [h_len], ?_⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← eq]
  show Stack.Pop (x :: y :: topics) s.stack s₅.stack
  rw [h_s₅, ← hb.stack]
  exact hp

lemma of_run_address {e : Sevm} {s s' : Devm} (h : Ninst.Run e s address s') :
    Devm.PushBurn [e.currentTarget.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- Value-carrying inversion for SELFBALANCE. -/
lemma of_run_selfbalance {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s selfbalance s') :
    Devm.PushBurn [s.getBal e.currentTarget] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_retdatasize {e : Sevm} {s s' : Devm} (h : Ninst.Run e s retdatasize s') :
    ∃ x, Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact ⟨_, Devm.pushBurn_of_pushItem run⟩

lemma of_run_gas {e : Sevm} {s s' : Devm} (h : Ninst.Run e s gas s') :
    ∃ x, Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact ⟨_, Devm.pushBurn_of_burn_of_push (Devm.burn_of_chargeGas h1) (Devm.push_of_push h2)⟩

lemma of_run_mload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mload s') :
    ∃ x y, Stack.Diff [x] [y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, hpop⟩
  have hb := Devm.burn_of_chargeGas h2
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] (s₂.memRead si 32).2 s' :=
    ⟨_, Devm.push_of_push run₂⟩
  refine ⟨x, val, s₁.stack, hpop.stack, ?_⟩
  rw [show s₁.stack = s₂.stack from hb.stack, ← Devm.memRead_stack s₂ si 32]
  exact hpush.stack

lemma of_run_retdatacopy {e : Sevm} {s s' : Devm} (h : Ninst.Run e s retdatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨z, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  refine ⟨x, y, z, ?_⟩
  split at h5
  · cases h5
  · injection h5 with eq
    have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq]
    show Stack.Pop [x, y, z] s.stack s₄.stack
    rw [← hb.stack]
    exact hp

/-- On the successful path the CALL-family return pushes the status flag onto
the parent's stack; incorporating the child and the memory write leave the
stack alone.  The stack-side companion of `Resume.call_state`, needed by a
caller that continues executing after the call returns.  It lives here, below
`Devm.push_of_push`, rather than beside its `state` sibling. -/
lemma Resume.call_stack {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    ∃ b, sf.stack = b :: parent.stack := by
  have key : ∀ d : Devm, d.stack = parent.stack → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      ∃ b, sf.stack = b :: parent.stack := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      refine ⟨v, ?_⟩
      have h_push := (Devm.push_of_push hp).stack
      show evm2.stack = _
      rw [h_push, hd]
      rfl
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

lemma Stack.swapCore_of_swap {n} {xxs yys : Stack} (h : Swap n xxs yys) :
    ∃ x y xs ys, xxs = x :: xs ∧ yys = y :: ys ∧ SwapCore x y n xs ys := by
  cases xxs; cases h; cases yys; cases h; refine ⟨_, _, _, _, rfl, rfl, h⟩

lemma Stack.swapCore_zero {x y s} : SwapCore x y 0 (y :: s) (x :: s) := by simp [SwapCore]

lemma Stack.swapCore_succ {n x y z s s'} :
    SwapCore x z n s s' → SwapCore x z (n + 1) (y :: s) (y :: s') := by simp [SwapCore]

lemma Stack.swapCore_getElem_set {x y : B256} {n : Nat} {xs xs' : Stack}
    (h : SwapCore x y n xs xs') (t : Stack) :
    (xs ++ t)[n]? = some y ∧ (xs ++ t).set n x = xs' ++ t := by
  induction n generalizing xs xs' with
  | zero =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hx, hy, hl⟩
    subst hx; subst hy; subst hl
    constructor <;> rfl
  | succ n ih =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hz, h⟩
    subst hz
    rcases ih h with ⟨h1, h2⟩
    constructor
    · simpa using h1
    · simp only [List.cons_append, List.set_cons_succ]
      rw [h2]

lemma Stack.prefix_of_swap {n} {xs xs' stk stk' : Stack} :
    Swap n xs xs' → List.swap stk n = some stk' → (xs <<+ stk) → (xs' <<+ stk') := by
  intro h0 h1 h2
  rcases swapCore_of_swap h0 with ⟨x, y, xs₀, ys₀, hxs, hys, hc⟩
  subst hxs; subst hys
  rcases h2 with ⟨t, h2⟩
  rw [show stk = (x :: xs₀) ++ t from h2] at h1
  rcases swapCore_getElem_set hc t with ⟨hget, hset⟩
  simp only [List.cons_append, List.swap, hget, hset] at h1
  injection h1 with h1
  refine ⟨t, ?_⟩
  rw [← h1]
  rfl

lemma Stack.nth_getElem {n : Nat} {x : B256} {xs ys : Stack}
    (h : Nth n x xs) (h' : xs <<+ ys) : ys[n]? = some x := by
  revert h'
  induction h generalizing ys with
  | head z zs =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (z :: zs) ++ t from h']; rfl
  | tail m z w zs h ih =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (w :: zs) ++ t from h']
    simp only [List.cons_append, List.getElem?_cons_succ]
    exact ih ⟨t, rfl⟩

lemma prefix_of_diffBurn_one (v : B256 → B256) {x xs} {s s' : Devm} :
    (∃ x', Devm.DiffBurn [x'] [v x'] s s') →
    (x :: xs <<+ s.stack) → (v x :: xs <<+ s'.stack) := by show_prefix_one

lemma prefix_of_diffBurn_two (v : B256 → B256 → B256) {x y xs} {s s' : Devm} :
    (∃ x' y', Devm.DiffBurn [x', y'] [v x' y'] s s') →
    (x :: y :: xs <<+ s.stack) → (v x y :: xs <<+ s'.stack) := by show_prefix_two

lemma prefix_of_not {e} {x xs} {s s' : Devm} :
    Ninst.Run e s not s' → (x :: xs <<+ s.stack) → ((~~~ x) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (~~~ ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_iszero {e} {x xs} {s s' : Devm} :
    Ninst.Run e s iszero s' → (x :: xs <<+ s.stack) → ((x =? 0) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (· =? 0) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_eq {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s eq s' → (x :: y :: xs <<+ s.stack) → ((x =? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.eqCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_lt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s lt s' → (x :: y :: xs <<+ s.stack) → ((x <? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.ltCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_gt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s gt s' → (x :: y :: xs <<+ s.stack) → ((x >? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.gtCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shl {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shl s' → (x :: y :: xs <<+ s.stack) → (y <<< x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y <<< x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shr {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shr s' → (x :: y :: xs <<+ s.stack) → (y >>> x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y >>> x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_or {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s or s' → (x :: y :: xs <<+ s.stack) → ((x ||| y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.or ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

/-- Bitwise conjunction on EVM words is commutative. -/
theorem B256.and_comm (x y : B256) : x &&& y = y &&& x := by
  rcases x with ⟨⟨xh0, xh1⟩, ⟨xl0, xl1⟩⟩
  rcases y with ⟨⟨yh0, yh1⟩, ⟨yl0, yl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.and_comm _ _

/-- Bitwise exclusive-or on EVM words is commutative. -/
theorem B256.xor_comm (x y : B256) : x ^^^ y = y ^^^ x := by
  rcases x with ⟨⟨xh0, xh1⟩, ⟨xl0, xl1⟩⟩
  rcases y with ⟨⟨yh0, yh1⟩, ⟨yl0, yl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.xor_comm _ _

/-- Reapplying the same bitwise mask does not change an EVM word. -/
theorem B256.and_idem_right (x mask : B256) :
    (x &&& mask) &&& mask = x &&& mask := by
  rcases x with ⟨xh, xl⟩
  rcases mask with ⟨mh, ml⟩
  change ⟨(xh &&& mh) &&& mh, (xl &&& ml) &&& ml⟩ =
    (⟨xh &&& mh, xl &&& ml⟩ : B256)
  apply Prod.ext
  · rcases xh with ⟨xh0, xh1⟩
    rcases mh with ⟨mh0, mh1⟩
    change ⟨(xh0 &&& mh0) &&& mh0, (xh1 &&& mh1) &&& mh1⟩ =
      (⟨xh0 &&& mh0, xh1 &&& mh1⟩ : B128)
    apply Prod.ext
    · change (xh0 &&& mh0) &&& mh0 = xh0 &&& mh0
      rw [UInt64.and_assoc, UInt64.and_self]
    · change (xh1 &&& mh1) &&& mh1 = xh1 &&& mh1
      rw [UInt64.and_assoc, UInt64.and_self]
  · rcases xl with ⟨xl0, xl1⟩
    rcases ml with ⟨ml0, ml1⟩
    change ⟨(xl0 &&& ml0) &&& ml0, (xl1 &&& ml1) &&& ml1⟩ =
      (⟨xl0 &&& ml0, xl1 &&& ml1⟩ : B128)
    apply Prod.ext
    · change (xl0 &&& ml0) &&& ml0 = xl0 &&& ml0
      rw [UInt64.and_assoc, UInt64.and_self]
    · change (xl1 &&& ml1) &&& ml1 = xl1 &&& ml1
      rw [UInt64.and_assoc, UInt64.and_self]

/-- `XOR` replaces the two known stack heads by their exclusive-or. -/
lemma prefix_of_xor {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s xor s' → (x :: y :: xs <<+ s.stack) →
      ((x ^^^ y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.xor ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_and {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s and s' → (x :: y :: xs <<+ s.stack) → ((x &&& y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.and ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_add {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s add s' → (x :: y :: xs <<+ s.stack) → ((x + y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· + ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_sub {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sub s' → (x :: y :: xs <<+ s.stack) → ((x - y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· - ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_mul {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mul s' → (x :: y :: xs <<+ s.stack) → ((x * y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· * ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_div {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s div s' → (x :: y :: xs <<+ s.stack) → ((x / y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· / ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_mod {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mod s' → (x :: y :: xs <<+ s.stack) → ((x % y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· % ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_push {xs ys} {s s' : Devm} :
    Devm.PushBurn xs s s' → (ys <<+ s.stack) → ((xs ++ ys) <<+ s'.stack) :=
  λ h0 h1 => append_pref h0.stack h1

/-- `TIMESTAMP` pushes the current block time above any known stack prefix. -/
lemma prefix_of_timestamp {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (h : Ninst.Run e s timestamp s') :
    e.benvStat.time :: xs <<+ s'.stack := by
  change Ninst.Run e s (.reg .timestamp) s' at h
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact prefix_of_push (Devm.pushBurn_of_pushItem run) hp

/-- `DUP n` at a stack whose top `n + 1` words are already known: the word it
pushes is the one the walk knows sits at index `n`.

The value-carrying `DUP`.  Every existing walk re-derives this inline —
`of_run_dup`, then `Stack.nth_getElem` to pin the anonymous word, then
`prefix_of_push` — which is three steps and a `subst` per `DUP`, and `flashLoan`
alone has nine.  The `Stack.Nth` premise is discharged by `show_nth`. -/
lemma prefix_of_dup_val {e : Sevm} {s s' : Devm} {n : Fin 16} {x : B256} {xs : Stack}
    (h : Ninst.Run e s (dup n) s') (hnth : Stack.Nth n.val x xs) (hp : xs <<+ s.stack) :
    x :: xs <<+ s'.stack := by
  rcases of_run_dup h with ⟨y, hy, pb⟩
  rw [Stack.nth_getElem hnth hp] at hy
  injection hy with hy
  subst hy
  exact prefix_of_push pb hp

lemma prefix_of_pop {y : B256} {xs} {s s' : Devm} :
    (∃ x, Devm.PopBurn [x] s s') → (y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h h'; rcases h with ⟨x, hx⟩
  have h_eq : y = x :=
    (List.of_cons_pref_of_cons_pref h' (pref_of_split hx.stack)).left
  rw [h_eq] at h'
  exact of_append_pref hx.stack h'

lemma prefix_of_mstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_mstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_sstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_sstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_calldatacopy {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s calldatacopy s' → (x :: y :: z :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_calldatacopy h0 with ⟨x', y', z', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- Value-carrying `prefix_of_calldataload`: the word left on the stack is the
calldata word at the offset that was there before. Modelled on
`prefix_of_sload`, which already carries its value this way. -/
lemma prefix_of_calldataload_val {e} {x xs} {s s' : Devm} :
    Ninst.Run e s calldataload s' → (x :: xs <<+ s.stack) →
    (Sevm.dataWord e x :: xs <<+ s'.stack) := by
  intro h0 h1
  rcases of_run_calldataload_val h0 with ⟨x', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  exact append_pref h3 (of_append_pref h2 h1)

lemma prefix_of_calldataload {e} {x xs} {s s' : Devm} :
    Ninst.Run e s calldataload s' → (x :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack :=
  fun h0 h1 => ⟨_, prefix_of_calldataload_val h0 h1⟩

lemma prefix_of_kec {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s kec s' → (x :: y :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_kec h0 with ⟨x', y', z', stk, h2, h3⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact ⟨z', append_pref h3 (of_append_pref h2 h1)⟩

/-- Value-carrying `prefix_of_cdl`: `cdl n` leaves the calldata word at byte
offset `n` on top of the stack. -/
lemma prefix_of_cdl_val {e n xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (cdl n) s' →
    (Sevm.dataWord e n :: xs <<+ s'.stack) := by
  intro h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s₁, h_push, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨s₂, h_cdl, h_nil⟩
  cases h_nil
  have h1 : n :: xs <<+ s₁.stack := prefix_of_push (of_run_pushB256 h_push) h_pfx
  exact prefix_of_calldataload_val h_cdl h1

lemma prefix_of_cdl {e n xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (cdl n) s' → ∃ z, z :: xs <<+ s'.stack :=
  fun h_pfx h_run => ⟨_, prefix_of_cdl_val h_pfx h_run⟩

/-- The `of_arg` the decoding layer reads through: running `arg k` leaves the
`k`-th head word of the argument area on the stack.

`arg k` is `cdl (32 * k + 4)` and `Sevm.argWord e k` is `Sevm.dataWord e
(32 * k + 4)`, both by definition, so this is `prefix_of_cdl_val` at a
definitional instance rather than a new argument. Head-word access, not ABI
decoding: for a dynamic argument the word delivered here is the tail's offset
(see `arg`'s note (1) and `forwardArgTail`). -/
lemma prefix_of_arg {e k xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (arg k) s' →
    (Sevm.argWord e k :: xs <<+ s'.stack) :=
  prefix_of_cdl_val

/-- `EXTCODESIZE` at a known stack top, with the exact code-size word read
from the instruction's input state.  Address warming may change the state
metadata, but memory is untouched. -/
lemma prefix_of_extcodesize_val
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Ninst.Run e s Ninst.extcodesize r) :
    ((s.getCode x.toAdr).size.toB256 :: xs <<+ r.stack) ∧
      s.memory = r.memory := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨adr, d1⟩, hpopAdr, hrun⟩
  rw [Devm.popToAdr_def] at hpopAdr
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hpopAdr
  rcases hpop : Devm.pop s with _ | ⟨word, d0⟩ <;>
    simp [hpop] at hpopAdr
  rcases hpopAdr with ⟨rfl, rfl⟩
  have hpop' := Devm.pop_of_pop hpop
  have hx : x = word :=
    (List.of_cons_pref_of_cons_pref hp
      (pref_of_split hpop'.stack)).left
  subst word
  have htail : xs <<+ d0.stack := of_append_pref hpop'.stack hp
  split at hrun
  · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hst : s.state = d2.state :=
      hpop'.state.trans (Devm.burn_of_chargeGas hgas).state
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct
      rw [hst]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((Devm.burn_of_chargeGas hgas).memory.trans
          (Devm.push_of_push hpush).memory)
  · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hst : s.state = d2.state :=
      hpop'.state.trans
        ((show d0.state = (addAccessedAddress d0 x.toAdr).state from rfl).trans
          (Devm.burn_of_chargeGas hgas).state)
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct
      rw [hst]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((show d0.memory = (addAccessedAddress d0 x.toAdr).memory from rfl).trans
          ((Devm.burn_of_chargeGas hgas).memory.trans
            (Devm.push_of_push hpush).memory))

/-! ### Reading a described calldata layout

The bridge between `Sevm.dataWord` — what the contract's `calldataload` actually
yields — and a calldata *described* as an explicit concatenation, which is how
`abiCallWithTail` states a canonical encoding. Without this the encoding
definition and the reader would be two unrelated pieces of syntax and the
decoding predicate would carry no information. -/

/-- The word at `idx` of a calldata that has `pre` before it and a whole word
`w` at it. Note `post` is unconstrained: nothing about the rest of the calldata
is needed, which is what lets the head words be read one at a time. -/
lemma dataWord_of_append {e : Sevm} {idx : B256} {pre post : Bytes} {w : B256}
    (hlen : idx.toNat = pre.length)
    (hdata : e.data = pre ++ (B256.toBytes w ++ post)) :
    Sevm.dataWord e idx = w := by
  simp only [Sevm.dataWord, hdata, List.sliceD]
  rw [List.drop_length_append' hlen,
      List.takeD_eq_take _ (by simp [List.length_append, B256.length_toBytes]),
      List.take_length_append' (B256.length_toBytes w).symm, B256.toB256_toBytes]

/-- `fsig` leaves the calldata's function selector on the stack.

The entry route's first fact, and the one Step 2 of the arc composes with
dispatch reachability: `dispatchWith` assumes the selector is already on top of
the stack, and until now nothing said *which* word that was. Note that
`prefix_of_shr` was already value-carrying — only the calldata inversions were
not, which is why this fact was previously unavailable. -/
lemma prefix_of_fsig {e xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s fsig s' → (Sevm.selector e :: xs <<+ s'.stack) := by
  intro h_pfx h_run
  rcases of_run_append (cdl 0) h_run with ⟨s₁, h_cdl, h_shr⟩
  have h1 : Sevm.dataWord e 0 :: xs <<+ s₁.stack := prefix_of_cdl_val h_pfx h_cdl
  rcases Line.of_run_cons h_shr with ⟨s₂, h_push, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨s₃, h_op, h_nil⟩
  cases h_nil
  exact prefix_of_shr h_op (prefix_of_push (of_run_pushB256 h_push) h1)

lemma abiSelectorBytes_length (sel : B256) : (abiSelectorBytes sel).length = 4 := by
  simp [abiSelectorBytes, B256.length_toBytes]

private lemma UInt64.high_concat32 (x y : UInt32) :
    ((((x.toUInt64 <<< 32) ||| y.toUInt64) >>> 32).toUInt32) = x := by
  rw [← UInt32.toNat_inj]
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo]
  have widen (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  rw [widen, widen, n32]
  have hx : x.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have := UInt32.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 32 (UInt32.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt32.toNat_lt x)]

private lemma UInt64.low_concat32 (x y : UInt32) :
    (((x.toUInt64 <<< 32) ||| y.toUInt64).toUInt32) = y := by
  rw [← UInt32.toNat_inj]
  rw [UInt64.toNat_toUInt32]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo]
  have widen (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  rw [widen, widen, n32]
  have hx : x.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have := UInt32.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt32.toNat_lt y), Nat.zero_or]

private lemma UInt32.high_concat16 (x y : UInt16) :
    ((((x.toUInt32 <<< 16) ||| y.toUInt32) >>> 16).toUInt16) = x := by
  rw [← UInt16.toNat_inj]
  rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo]
  have widen (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  rw [widen, widen, n16]
  have hx : x.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := UInt16.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 16 (UInt16.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt16.toNat_lt x)]

private lemma UInt32.low_concat16 (x y : UInt16) :
    (((x.toUInt32 <<< 16) ||| y.toUInt32).toUInt16) = y := by
  rw [← UInt16.toNat_inj]
  rw [UInt32.toNat_toUInt16]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo]
  have widen (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  rw [widen, widen, n16]
  have hx : x.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := UInt16.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt16.toNat_lt y), Nat.zero_or]

private lemma UInt16.high_concat8 (x y : UInt8) :
    ((((x.toUInt16 <<< 8) ||| y.toUInt16) >>> 8).toUInt8) = x := by
  rw [← UInt8.toNat_inj]
  rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft_lo]
  have widen (z : UInt8) : z.toUInt16.toNat = z.toNat := rfl
  have n8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [widen, widen, n8]
  have hx : x.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have := UInt8.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 8 (UInt8.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt8.toNat_lt x)]

private lemma UInt16.low_concat8 (x y : UInt8) :
    (((x.toUInt16 <<< 8) ||| y.toUInt16).toUInt8) = y := by
  rw [← UInt8.toNat_inj]
  rw [UInt16.toNat_toUInt8]
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft_lo]
  have widen (z : UInt8) : z.toUInt16.toNat = z.toNat := rfl
  have n8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [widen, widen, n8]
  have hx : x.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have := UInt8.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt8.toNat_lt y), Nat.zero_or]

/-- Encoding eight bytes as a limb and decoding it again is exact. -/
private lemma UInt64.toBytes_ofBytes (a b c d e f g h : UInt8) :
    (UInt64.ofBytes a b c d e f g h).toBytes = [a, b, c, d, e, f, g, h] := by
  rw [UInt64.ofBytes_eq_halves]
  simp only [UInt64.toBytes, UInt64.high_concat32, UInt64.low_concat32,
    UInt32.toBytes]
  rw [UInt32.ofBytes_eq_halves, UInt32.ofBytes_eq_halves]
  simp only [UInt32.high_concat16, UInt32.low_concat16, UInt16.toBytes,
    UInt16.ofBytes, UInt16.high_concat8, UInt16.low_concat8]
  simp

/-- The 32-byte codec is an exact round trip, in the concrete shape used by
`Bytes.toBytes_toB256_of_length`. -/
private lemma Bytes.toBytes_toB256_32
    (a00 a01 a02 a03 a04 a05 a06 a07
     a08 a09 a10 a11 a12 a13 a14 a15
     a16 a17 a18 a19 a20 a21 a22 a23
     a24 a25 a26 a27 a28 a29 a30 a31 : UInt8) :
    (Bytes.toB256
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15,
       a16, a17, a18, a19, a20, a21, a22, a23,
       a24, a25, a26, a27, a28, a29, a30, a31]).toBytes =
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15,
       a16, a17, a18, a19, a20, a21, a22, a23,
       a24, a25, a26, a27, a28, a29, a30, a31] := by
  simp only [Bytes.toB256]
  rw [Bytes.toB256_go_eight_cons, Bytes.toB256_go_eight_cons,
      Bytes.toB256_go_eight_cons, Bytes.toB256_go_eight_cons]
  simp only [Bytes.toB256.go, B256.toBytes, B128.toBytes, List.append_assoc,
    UInt64.toBytes_ofBytes]
  simp

/-- `Bytes.toB256` loses no information on an exact word. -/
lemma Bytes.toBytes_toB256_of_length {xs : Bytes} (h : xs.length = 32) :
    (Bytes.toB256 xs).toBytes = xs := by
  rcases xs with _ | ⟨a00, xs⟩
  · simp at h
  rcases xs with _ | ⟨a01, xs⟩
  · simp at h
  rcases xs with _ | ⟨a02, xs⟩
  · simp at h
  rcases xs with _ | ⟨a03, xs⟩
  · simp at h
  rcases xs with _ | ⟨a04, xs⟩
  · simp at h
  rcases xs with _ | ⟨a05, xs⟩
  · simp at h
  rcases xs with _ | ⟨a06, xs⟩
  · simp at h
  rcases xs with _ | ⟨a07, xs⟩
  · simp at h
  rcases xs with _ | ⟨a08, xs⟩
  · simp at h
  rcases xs with _ | ⟨a09, xs⟩
  · simp at h
  rcases xs with _ | ⟨a10, xs⟩
  · simp at h
  rcases xs with _ | ⟨a11, xs⟩
  · simp at h
  rcases xs with _ | ⟨a12, xs⟩
  · simp at h
  rcases xs with _ | ⟨a13, xs⟩
  · simp at h
  rcases xs with _ | ⟨a14, xs⟩
  · simp at h
  rcases xs with _ | ⟨a15, xs⟩
  · simp at h
  rcases xs with _ | ⟨a16, xs⟩
  · simp at h
  rcases xs with _ | ⟨a17, xs⟩
  · simp at h
  rcases xs with _ | ⟨a18, xs⟩
  · simp at h
  rcases xs with _ | ⟨a19, xs⟩
  · simp at h
  rcases xs with _ | ⟨a20, xs⟩
  · simp at h
  rcases xs with _ | ⟨a21, xs⟩
  · simp at h
  rcases xs with _ | ⟨a22, xs⟩
  · simp at h
  rcases xs with _ | ⟨a23, xs⟩
  · simp at h
  rcases xs with _ | ⟨a24, xs⟩
  · simp at h
  rcases xs with _ | ⟨a25, xs⟩
  · simp at h
  rcases xs with _ | ⟨a26, xs⟩
  · simp at h
  rcases xs with _ | ⟨a27, xs⟩
  · simp at h
  rcases xs with _ | ⟨a28, xs⟩
  · simp at h
  rcases xs with _ | ⟨a29, xs⟩
  · simp at h
  rcases xs with _ | ⟨a30, xs⟩
  · simp at h
  rcases xs with _ | ⟨a31, xs⟩
  · simp at h
  cases xs with
  | nil =>
      simpa using (Bytes.toBytes_toB256_32 a00 a01 a02 a03 a04 a05 a06 a07
        a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
        a24 a25 a26 a27 a28 a29 a30 a31)
  | cons a32 xs => simp at h

private lemma Bytes.toB256_uint32_toBytes (x : UInt32) :
    Bytes.toB256 x.toBytes = x.toB256 := by
  have highZero : (x.toUInt64 >>> 32).toUInt32 = 0 := by
    rw [← UInt32.toNat_inj, UInt64.toNat_toUInt32,
      UInt64.toNat_shiftRight]
    change (x.toNat >>> 32) % 4294967296 = 0
    rw [Nat.shiftRight_eq_zero _ _ (UInt32.toNat_lt x)]
  have roundtrip := B256.toB256_toBytes
    (⟨⟨(0 : UInt64), 0⟩, ⟨0, x.toUInt64⟩⟩ : B256)
  change Bytes.toB256 x.toBytes =
    (⟨⟨(0 : UInt64), 0⟩, ⟨0, x.toUInt64⟩⟩ : B256)
  simpa [UInt32.toB256, B256.toBytes, B128.toBytes, UInt64.toBytes,
    UInt32.toBytes, UInt16.toBytes, highZero,
    Bytes.toB256_zero_cons] using roundtrip

/-- Shifting a word down by 224 bits is its first four big-endian bytes,
repacked as a `B256`. -/
lemma shiftRight_224_eq_toB256_take_four (x : B256) :
    x >>> 224 = Bytes.toB256 (x.toBytes.take 4) := by
  rcases x with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  have firstFour :
      (B256.toBytes (⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩ : B256)).take 4 =
        (x3 >>> 32).toUInt32.toBytes := by
    simp only [B256.toBytes, B128.toBytes, UInt64.toBytes]
    simp only [List.append_assoc]
    rw [List.take_length_append' (UInt32.length_toBytes _).symm]
  rw [firstFour, Bytes.toB256_uint32_toBytes]
  change B256.shiftRight (⟨⟨_, _⟩, ⟨_, _⟩⟩ : B256) 224 = _
  simp only [B256.shiftRight]
  change (⟨0, B128.shiftRight ⟨_, _⟩ 96⟩ : B256) = _
  simp only [B128.shiftRight]
  norm_num
  congr 3
  have hlt : (x3 >>> 32).toNat < 4294967296 := by
    rw [UInt64.toNat_shiftRight]
    change x3.toNat >>> 32 < 4294967296
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    have hx := UInt64.toNat_lt x3
    omega
  rw [← UInt64.toNat_inj]
  change (x3 >>> 32).toNat = (x3 >>> 32).toUInt32.toNat
  rw [UInt64.toUInt32_toNat, Nat.mod_eq_of_lt hlt]

/-- Taking a shorter prefix after a padded take is the shorter padded take. -/
lemma List.take_takeD_of_le {alpha} (xs : List alpha) (m n : Nat)
    (default : alpha) (le : m ≤ n) :
    (List.takeD n xs default).take m = List.takeD m xs default := by
  induction m generalizing n xs with
  | zero => rfl
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases xs with
          | nil =>
              simp only [List.takeD, List.tail, List.take, List.cons.injEq]
              exact ⟨trivial, ih [] n (by omega)⟩
          | cons x xs =>
              simp only [List.takeD, List.tail, List.take, List.cons.injEq]
              exact ⟨trivial, ih xs n (by omega)⟩

/-- `Sevm.selector` is exactly the first four calldata bytes, padded on the
right with zeros when calldata is short. -/
theorem Sevm.selector_eq_toB256_takeD_four (sevm : Sevm) :
    Sevm.selector sevm = Bytes.toB256 (sevm.data.takeD 4 0) := by
  let word := sevm.data.sliceD 0 32 0
  have wordLength : word.length = 32 := List.takeD_length _ _ _
  have roundtrip : (Bytes.toB256 word).toBytes = word :=
    Bytes.toBytes_toB256_of_length wordLength
  have firstFour :
      (Bytes.toB256 word).toBytes.take 4 = sevm.data.takeD 4 0 := by
    rw [roundtrip]
    unfold word
    simp only [List.sliceD, List.drop_zero]
    exact List.take_takeD_of_le sevm.data 4 32 0 (by omega)
  rw [Sevm.selector, Sevm.dataWord]
  change Bytes.toB256 word >>> 224 = _
  rw [shiftRight_224_eq_toB256_take_four, firstFour]

/-- Calldata beginning with a canonical ABI selector has that selector under
`Sevm.selector`, independently of its tail.  The explicit canonicality premise
is essential: `abiSelectorBytes` keeps only the low four bytes of an arbitrary
`B256`, whereas `Sevm.selector` is itself a four-byte word. -/
theorem selector_eq_of_data_eq_abiSelectorBytes_append
    {sevm : Sevm} {selected : B256} {tail : Bytes}
    (canonical : Bytes.toB256 (abiSelectorBytes selected) = selected)
    (data : sevm.data = abiSelectorBytes selected ++ tail) :
    Sevm.selector sevm = selected := by
  let word := sevm.data.sliceD 0 32 0
  have wordLength : word.length = 32 := by
    exact List.takeD_length _ _ _
  have roundtrip : (Bytes.toB256 word).toBytes = word :=
    Bytes.toBytes_toB256_of_length wordLength
  have firstFour :
      (Bytes.toB256 word).toBytes.take 4 = abiSelectorBytes selected := by
    rw [roundtrip]
    unfold word
    simp only [List.sliceD, List.drop_zero]
    rw [List.take_takeD_of_le _ _ _ _ (by omega)]
    rw [List.takeD_eq_take _ (by
      simp [data, abiSelectorBytes_length])]
    rw [data, List.take_append_of_le_length]
    · exact List.take_of_length_le (by rw [abiSelectorBytes_length])
    · rw [abiSelectorBytes_length]
  rw [Sevm.selector, Sevm.dataWord]
  change Bytes.toB256 word >>> 224 = selected
  rw [shiftRight_224_eq_toB256_take_four, firstFour, canonical]

/-! The three head words and the offset word of a `flashLoan`-shaped call.

`flashLoan(address,address,uint256,bytes)` is three static heads then one
dynamic tail, so these four are the whole head area. Together they are what
makes `Sevm.DecodesCallWithTail` a *specification*: they say the contract's own
`arg 0`, `arg 1`, `arg 2` and `arg 3` recover exactly the arguments the encoding
was built from, which is the identity fixed decision 2 demands and the falsifier
for the encoding definition itself. -/

/-- The encoding's head area, right-associated so each head word can be read off
by `dataWord_of_append` after re-associating the prefix. -/
lemma decodes_split {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    e.data = abiSelectorBytes sel ++ (B256.toBytes a ++ (B256.toBytes b ++
      (B256.toBytes c ++ (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data)))) := by
  simpa [Sevm.DecodesCallWithTail, abiCallWithTail, List.append_assoc] using h

lemma argWord_zero_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) : Sevm.argWord e 0 = a :=
  dataWord_of_append (by rw [abiSelectorBytes_length]; rfl) (decodes_split h)

lemma argWord_one_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) : Sevm.argWord e 1 = b := by
  have hd : e.data = (abiSelectorBytes sel ++ B256.toBytes a) ++ (B256.toBytes b ++
      (B256.toBytes c ++ (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data))) := by
    rw [List.append_assoc]; exact decodes_split h
  exact dataWord_of_append
    (by rw [List.length_append, abiSelectorBytes_length, B256.length_toBytes]; rfl) hd

lemma argWord_two_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) : Sevm.argWord e 2 = c := by
  have hd : e.data = (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b) ++
      (B256.toBytes c ++ (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data)) := by
    rw [List.append_assoc, List.append_assoc]; exact decodes_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, abiSelectorBytes_length,
        B256.length_toBytes, B256.length_toBytes]; rfl) hd

/-- The offset word is `0x80`, and this is proved rather than assumed: it is the
one head word whose value the encoding's *shape* fixes. -/
lemma argWord_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.argWord e 3 = Nat.toB256 128 := by
  have hd : e.data =
      (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++ B256.toBytes c) ++
      (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc]; exact decodes_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, List.length_append,
        abiSelectorBytes_length, B256.length_toBytes, B256.length_toBytes,
        B256.length_toBytes]; rfl) hd

lemma of_run_sload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sload s') :
    ∃ x, Stack.Diff [x] [Devm.getStorVal s e.currentTarget x] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hpop := Devm.pop_of_pop h1
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  refine ⟨key, s₁.stack, hpop.stack, ?_⟩
  suffices H : ∀ (d : Devm) (c : Nat),
      Devm.getStor s₁ = Devm.getStor d → s₁.stack = d.stack →
      (chargeGas c d >>= fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) = .ok s' →
      Stack.Push [Devm.getStorVal s e.currentTarget key] s₁.stack s'.stack by
    split at run₁
    · exact H s₁ gasWarmAccess rfl rfl run₁
    · exact H (addAccessedStorageKey s₁ e.currentTarget key) gasColdSload
        (@addAccessedStorageKey_getStor s₁ e.currentTarget key).symm rfl run₁
  intro d c hgs hst run'
  rcases Except.bind_eq_ok run' with ⟨s₂, h2, run₂⟩
  have hpush := Devm.push_of_push run₂
  have hstk : d.stack = s₂.stack := (Devm.burn_of_chargeGas h2).stack
  have e2 : Devm.getStor d = Devm.getStor s₂ := chargeGas_getStor_eq h2
  have hval : Devm.getStorVal s₂ e.currentTarget key
      = Devm.getStorVal s e.currentTarget key := by
    show (Devm.getStor s₂ e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key
    rw [← e2, ← hgs, ← e1]
  rw [hst, hstk, ← hval]
  exact hpush.stack

lemma prefix_of_sload {e x xs} {s s' : Devm} :
    Ninst.Run e s sload s' → (x :: xs <<+ s.stack) →
    ∃ y, (y :: xs <<+ s'.stack) ∧ y = Devm.getStorVal s e.currentTarget x := by
  intro h0 h1
  rcases of_run_sload h0 with ⟨x', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  exact ⟨_, append_pref h3 (of_append_pref h2 h1), rfl⟩

lemma prefix_of_mload {e x xs} {s s' : Devm} :
    Ninst.Run e s mload s' → (x :: xs <<+ s.stack) → ∃ y, y :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_mload h0 with ⟨x', y', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  rw [hx] at h1
  exact ⟨y', append_pref h3 (of_append_pref h2 h1)⟩

lemma prefix_of_retdatacopy {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s retdatacopy s' → (x :: y :: z :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_retdatacopy h0 with ⟨x', y', z', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- `mstoreAt` consumes the top of the stack and touches memory only. -/
lemma prefix_of_mstoreAt {e : Sevm} {s s' : Devm} {k x xs}
    (h : Line.Run e s (mstoreAt k) s') (hp : x :: xs <<+ s.stack) : xs <<+ s'.stack := by
  rcases Line.of_run_cons h with ⟨u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨u2, qm, hnil⟩
  cases hnil
  exact prefix_of_mstore qm (prefix_of_push (of_run_pushB256 qp) hp)

/-- `retdataShorterThan` pushes one flag. -/
lemma of_retdataShorterThan {e : Sevm} {s s' : Devm} {n : B256} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (retdataShorterThan n) s') :
    ∃ y, y :: xs <<+ s'.stack := by
  simp only [retdataShorterThan] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : n :: xs <<+ u1.stack := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  rcases of_run_retdatasize q2 with ⟨rds, pb2⟩
  have hp2 : rds :: n :: xs <<+ u2.stack := prefix_of_push pb2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, hnil⟩
  cases hnil
  exact ⟨_, prefix_of_lt q3 hp2⟩

/-- `checkRetdataHead` copies the head word into memory, reads it back, and
pushes one comparison flag. -/
lemma of_checkRetdataHead {e : Sevm} {s s' : Devm} {w m : B256} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (checkRetdataHead w m) s') :
    ∃ y, y :: xs <<+ s'.stack := by
  simp only [checkRetdataHead, pushList, List.map] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : (32 : B256) :: xs <<+ u1.stack := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hp2 : (0 : B256) :: (32 : B256) :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hp3 : (m * 32) :: (0 : B256) :: (32 : B256) :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hp4 : xs <<+ u4.stack := prefix_of_retdatacopy q4 hp3
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hp5 : (m * 32) :: xs <<+ u5.stack := prefix_of_push (of_run_pushB256 q5) hp4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  rcases prefix_of_mload q6 hp5 with ⟨head, hp6⟩
  rcases Line.of_run_cons h with ⟨u7, q7, h⟩
  have hp7 : w :: head :: xs <<+ u7.stack := prefix_of_push (of_run_pushB256 q7) hp6
  rcases Line.of_run_cons h with ⟨u8, q8, hnil⟩
  cases hnil
  exact ⟨_, prefix_of_eq q8 hp7⟩

lemma Line.spx_scheme {e s' i l xs xs' ys}
    (h : ∀ s0 s1, Ninst.Run e s0 i s1 → (xs <<+ s0.stack) → (xs' <<+ s1.stack))
    (h' : ∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (i :: l) s' → (ys <<+ s'.stack) := by
  intros s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h' s_mid (h _ _ h_head h_pfx) h_tail

lemma Line.spx_push {e : Sevm} {s' l bs p xs ys} :
    (∀ s : Devm, (bs.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (push bs p :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_push h_head) h_pfx

lemma Line.spx_pushB256 {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (pushB256 x :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_pushB256 h_head) h_pfx

lemma Line.spx_mstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (mstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_mstore

lemma Line.spx_sstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sstore

lemma Line.spx_dup {e s' l xs ys} {n : Fin 16} (x) :
    Stack.Nth n.val x xs →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (dup n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_nth; apply Line.spx_scheme
  intros s0 s1 h_step h_pfx
  rcases of_run_dup h_step with ⟨w, h_get, h_pb⟩
  rw [Stack.nth_getElem h_nth h_pfx] at h_get
  injection h_get with h_get
  rw [h_get]
  apply prefix_of_push h_pb h_pfx

lemma Line.spx_log (zs : Stack) {e s' l xs ys} {n : Fin 5} :
    zs.length = n.val + 2 →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (zs ++ xs <<+ s.stack) → Line.Run e s (log n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_len; apply Line.spx_scheme
  intros s₀ s₁ h_step h_pfx
  rcases of_run_log h_step with ⟨zs', h_len', h_pop⟩
  have h_zs : (zs <<+ s₀.stack) := @pref_trans _ zs (zs ++ xs) _ ⟨xs, rfl⟩ h_pfx
  have h_zs' : (zs' <<+ s₀.stack) := pref_of_split h_pop
  cases List.pref_unique (Eq.trans h_len h_len'.symm) h_zs h_zs'
  exact of_append_pref h_pop h_pfx

lemma Line.spx_swap (xs') {e s' l xs ys} {n : Fin 16} :
    Stack.Swap n.val xs xs' →
    (∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (swap n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_swap; apply Line.spx_scheme
  intros s0 s1 h_step
  exact Stack.prefix_of_swap h_swap (of_run_swap h_step)

lemma Line.spx_iszero {e s' l} {x} {xs ys} :
    (∀ s : Devm, ((x =? 0) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (iszero :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_iszero

lemma Line.spx_pop {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (pop :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step
  exact prefix_of_pop (of_run_pop h_step)

lemma Line.spx_eq {e s' l x y xs ys} :
    (∀ s : Devm, ((x =? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (eq :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_eq

lemma Line.spx_lt {e s' l x y xs ys} :
    (∀ s : Devm, ((x <? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (lt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_lt

lemma Line.spx_gt {e s' l x y xs ys} :
    (∀ s : Devm, ((x >? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (gt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_gt

lemma Line.spx_sub {e s' l x y xs ys} :
    (∀ s : Devm, ((x - y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sub :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sub

lemma Line.spx_not {e s' l x xs ys} :
    (∀ s : Devm, (~~~ x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (not :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_not

lemma Line.spx_or {e s' l x y xs ys} :
    (∀ s : Devm, ((x ||| y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (or :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_or

lemma Line.spx_and {e s' l x y xs ys} :
    (∀ s : Devm, ((x &&& y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (and :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_and

lemma Line.spx_shl {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y <<< x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shl :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shl

lemma Line.spx_shr {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y >>> x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shr :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shr

lemma Line.spx_add {e s' l x y xs ys} :
    (∀ s : Devm, ((x + y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (add :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_add

lemma Line.spx_caller {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.caller.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (caller :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_caller h_step) h_pfx

lemma Line.spx_callvalue {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.value :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (callvalue :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_callvalue h_step) h_pfx

lemma Line.spx_calldatacopy {e : Sevm} {s' l x y z xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: z :: xs <<+ s.stack) → Line.Run e s (calldatacopy :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_calldatacopy

lemma Line.spx_unwrap {e xs} {s' : Devm} :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s [] s' → (xs <<+ s'.stack) := by
  intros _ h0 h1; cases h1; apply h0


/-- `logWith 2 0 1` pops the topic triple and the window pair. -/
lemma of_logWith201 {e : Sevm} {s s' : Devm} {ev z w : B256} {xs}
    (hp : ev :: z :: w :: xs <<+ s.stack) (h : Line.Run e s (logWith 2 0 1) s') :
    xs <<+ s'.stack := by
  generalize_line_prefix


lemma memRead_getBal_eq {x n : Nat} {devm devm' : Devm} {value : Bytes} (h : devm.memRead x n = ⟨value, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

/-- Successful-run observation invariant retained as the public projection of
the canonical regular-instruction effect theorems. -/
def Rinst.Inv {ξ : Type} (f : Devm → ξ) (r : Rinst) : Prop :=
  ∀ {pc sevm pre post}, Rinst.run ⟨pc, sevm, pre⟩ r = (.ok post) → f pre = f post

lemma Rinst.preserves_bal {r} : Rinst.Inv Devm.getBal r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf; exact funext hf.getBal_eq
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact congrArg (fun s => s.bal) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact funext hf.getBal

/-- A regular instruction other than the two world-writing stores preserves
the complete persistent world state.  Specific `Hinv` instances below expose
the cases needed by WETH10's shared nonpayable entry wrapper. -/
lemma Rinst.preserves_state {r}
    (h_not_sstore : r ≠ Rinst.sstore)
    (h_not_tstore : r ≠ Rinst.tstore) :
    Rinst.Inv Devm.state r := by
  intro pc sevm pre post hrun
  have hf := Rinst.run_instructionFrame pc sevm pre r
    h_not_sstore h_not_tstore
  rw [hrun] at hf
  exact hf.state

lemma memRead_getStor_eq {x n : Nat} {devm devm' : Devm} {value : Bytes}
    (h : devm.memRead x n = ⟨value, devm'⟩) :
    Devm.getStor devm' = Devm.getStor devm := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma Rinst.preserves_stor {r} (h_not_sstore : r ≠ Rinst.sstore) : Rinst.Inv Devm.getStor r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact congrArg (fun s => fun a => (s.get a).stor) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r h_not_sstore ht; rw [hrun] at hf
    exact funext (Devm.InstructionFrame.getStor hf)

class Rinst.Hinv {ξ : Type} (f : Devm → ξ) (o : Rinst) where (inv : Rinst.Inv f o)

instance {ξ : Type} (f : Devm → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Ninst.Hinv f (Ninst.reg o) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact Rinst.Hinv.inv run.2.symm
⟩

instance {o : Rinst} : Rinst.Hinv Devm.getBal o := ⟨Rinst.preserves_bal⟩

instance : Rinst.Hinv Devm.state Rinst.callvalue :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

instance : Rinst.Hinv Devm.state Rinst.iszero :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

instance : Rinst.Hinv Devm.state Rinst.mstore :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

instance : Rinst.Hinv Devm.state Rinst.mload :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

/-- The whole persistent world state is preserved by every register
instruction except the two store forms; these are the cases the compiled
walks in this repository actually step through. -/
syntax "show_hinv_state" : tactic
macro_rules
  | `(tactic| show_hinv_state) =>
    `(tactic| exact ⟨Rinst.preserves_state (by intro h; cases h)
        (by intro h; cases h)⟩)

instance : Rinst.Hinv Devm.state Rinst.calldatasize := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.calldataload := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.calldatacopy := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.codesize := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.codecopy := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.lt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.gt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.add := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.mul := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.sub := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.and := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.or := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.not := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.eq := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.shl := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.shr := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.div := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.mod := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.exp := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.slt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.sgt := by show_hinv_state

/-- An observation preserved as a whole family is preserved at each index.  A
walk that only tracks one account's balance states its invariant as the
projection `fun d => d.getBal a`, so the family instances above are exposed at
that shape rather than restated per contract. -/
instance {a : Adr} {o : Rinst} : Rinst.Hinv (fun d => Devm.getBal d a) o :=
  ⟨by intro pc sevm pre post hrun; exact congrFun (Rinst.preserves_bal hrun) a⟩

instance {a : Adr} {i : Ninst} [Ninst.Hinv Devm.getBal i] :
    Ninst.Hinv (fun d => Devm.getBal d a) i :=
  ⟨by intros e s s' h; exact congrFun (Ninst.Hinv.inv h) a⟩

instance {o : Rinst} : Rinst.Hinv Devm.getCode o := ⟨by
  intro pc sevm pre post run
  funext a
  exact (Rinst.preserves_getCode run a).symm⟩

syntax "show_hinv_stor" : tactic
macro_rules
  | `(tactic| show_hinv_stor) =>
    `(tactic| exact ⟨Rinst.preserves_stor (by intro; contradiction)⟩)


instance : Rinst.Hinv Devm.getStor Rinst.add := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mul := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sub := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.div := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sdiv := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.smod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.addmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mulmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.exp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.signextend := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.lt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.slt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sgt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.eq := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.iszero := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.and := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.or := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.xor := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.not := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.byte := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shr := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shl := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sar := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.clz := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.kec := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.address := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.balance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.origin := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.caller := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.callvalue := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldataload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gasprice := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.retdatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.retdatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodehash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blockhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.coinbase := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.timestamp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.number := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.prevrandao := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gaslimit := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.chainid := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.selfbalance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.basefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobbasefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pop := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore8 := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mcopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pc := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.msize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gas := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.dup n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.swap n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.log n) := by show_hinv_stor

/-! ### `Ninst.Hinv` instances for the push and stack-scratch instructions

The `Rinst.Hinv` layer above covers every register instruction; these cover
the `Ninst` constructors that are not `reg` (`push`, `pushB256`, `dup`) plus
the `Devm.state` observable, which has no blanket `Rinst` instance because
`sstore` moves it.  They live here, with the rest of the `Hinv` API and the
`Ninst.run_push_eq` equation written for them, rather than in a contract's
own file: `line_inv` needs them wherever a dispatcher's scratch lines are
reasoned about, which is now `Ladder.lean`. -/

instance {x} : Ninst.Hinv Devm.getBal (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hc] at run; dsimp [bind, Except.bind] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      apply funext; intro a
      exact (chargeGas_getBal_eq hc a).symm.trans (Devm.push_getBal_eq hp a).symm
⟩

instance {x} : Ninst.Hinv Devm.getStor (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hc] at run; dsimp [bind, Except.bind] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      exact (chargeGas_getStor_eq hc).trans (Devm.push_getStor_eq hp)
⟩

instance {x} : Ninst.Hinv Devm.getCode (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hc] at run; dsimp [bind, Except.bind] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      apply funext; intro a
      exact (chargeGas_getCode_eq hc a).symm.trans (Devm.push_getCode_eq hp a).symm
⟩

instance {x} : Ninst.Hinv Devm.state (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  rcases h_pb with ⟨_, _, _, _, _, _, _, _, _, _, _, h_state, _⟩
  exact h_state
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getBal (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  funext a; simp only [Devm.getBal, Devm.getAcct]; rw [h_pb.state]
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getStor (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  funext a; simp only [Devm.getStor, Devm.getAcct]; rw [h_pb.state]
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getCode (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  funext a; simp only [Devm.getCode, Devm.getAcct]; rw [h_pb.state]
⟩

instance : Ninst.Hinv Devm.state (Ninst.reg Rinst.eq) := ⟨by
  intros e s s' h
  obtain ⟨pc, run⟩ := of_run_reg h
  dsimp [Rinst.run, Rinst.runCore] at run
  rw [applyBinary_def] at run
  rcases hp1 : Devm.pop s with _ | val1
  · rw [hp1] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hp1] at run; dsimp [bind, Except.bind] at run
    rcases val1 with ⟨x1, s1⟩
    rcases hp2 : Devm.pop s1 with _ | val2
    · rw [hp2] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hp2] at run; dsimp [bind, Except.bind] at run
      rcases val2 with ⟨x2, s2⟩
      rcases hpush : pushItem _ gVerylow s2 with _ | s''
      · rw [hpush] at run; contradiction
      · rw [hpush] at run
        injection run with h_eq; subst h_eq
        have h_pop1 := Devm.pop_of_pop hp1
        have h_pop2 := Devm.pop_of_pop hp2
        have h_push := Devm.pushBurn_of_pushItem hpush
        rcases h_pop1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩
        rcases h_pop2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs2, _⟩
        rcases h_push with ⟨_, _, _, _, _, _, _, _, _, _, _, hs3, _⟩
        exact hs1.trans (hs2.trans hs3)
⟩

instance {n} : Ninst.Hinv Devm.state (Ninst.dup n) := ⟨by
  intros e s s' h
  obtain ⟨pc, run⟩ := of_run_reg h
  dsimp [Rinst.run, Rinst.runCore] at run
  rcases hc : chargeGas gVerylow s with _ | s_gas
  · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hc] at run; dsimp [bind, Except.bind] at run
    split at run
    · contradiction
    · rename_i rh word
      have h_run_eq : (chargeGas gVerylow s >>= fun d => d.push rh) = .ok s' := by
        dsimp [bind, Except.bind]; rw [hc]; exact run
      have h_pb := Devm.pushBurn_of_run h_run_eq
      rcases h_pb with ⟨_, _, _, _, _, _, _, _, _, _, _, h_state, _⟩
      exact h_state
⟩

instance : Ninst.Hinv Devm.state (Ninst.reg Rinst.gt) := ⟨by
  intros e s s' h
  obtain ⟨pc, run⟩ := of_run_reg h
  dsimp [Rinst.run, Rinst.runCore] at run
  rw [applyBinary_def] at run
  rcases hp1 : Devm.pop s with _ | val1
  · rw [hp1] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hp1] at run; dsimp [bind, Except.bind] at run
    rcases val1 with ⟨x1, s1⟩
    rcases hp2 : Devm.pop s1 with _ | val2
    · rw [hp2] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hp2] at run; dsimp [bind, Except.bind] at run
      rcases val2 with ⟨x2, s2⟩
      rcases hpush : pushItem _ gVerylow s2 with _ | s''
      · rw [hpush] at run; contradiction
      · rw [hpush] at run
        injection run with h_eq; subst h_eq
        have h_pop1 := Devm.pop_of_pop hp1
        have h_pop2 := Devm.pop_of_pop hp2
        have h_push := Devm.pushBurn_of_pushItem hpush
        rcases h_pop1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩
        rcases h_pop2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs2, _⟩
        rcases h_push with ⟨_, _, _, _, _, _, _, _, _, _, _, hs3, _⟩
        exact hs1.trans (hs2.trans hs3)
⟩

/-! ### What each instruction does to memory

`Devm.memory` is preserved outright by every instruction except the three that
touch it, so the `line_inv` machinery carries a memory image across whole
`Line`s once these `Hinv` instances exist.  The three exceptions get
value-carrying inversions of their own, further down beside the `Mem` write
algebra.

The block sits *here*, beside the `Devm.state` / `Devm.getStor` / `Devm.getCode`
instances rather than with the `Mem` material, because instance resolution is
position-sensitive within a module and dispatch reachability — immediately below
— needs a memory image carried across the dispatcher's scratch instructions. -/

syntax "show_hinv_mem_binary" : tactic
macro_rules
  | `(tactic| show_hinv_mem_binary) =>
    `(tactic|
        refine ⟨?_⟩ <;>
        intro pc sevm pre post run <;>
        simp only [Rinst.run, Rinst.runCore] at run <;>
        exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.memory)

syntax "show_hinv_mem_unary" : tactic
macro_rules
  | `(tactic| show_hinv_mem_unary) =>
    `(tactic|
        refine ⟨?_⟩ <;>
        intro pc sevm pre post run <;>
        simp only [Rinst.run, Rinst.runCore] at run <;>
        exact (Devm.diffBurn_of_applyUnary run).choose_spec.memory)

syntax "show_hinv_mem_push" : tactic
macro_rules
  | `(tactic| show_hinv_mem_push) =>
    `(tactic|
        refine ⟨?_⟩ <;>
        intro pc sevm pre post run <;>
        simp only [Rinst.run, Rinst.runCore] at run <;>
        exact (Devm.pushBurn_of_pushItem run).memory)

instance : Rinst.Hinv Devm.memory Rinst.add := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.sub := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.lt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.gt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.eq := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.and := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.or := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.xor := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.shl := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.shr := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.mul := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.div := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.mod := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.sdiv := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.smod := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.slt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.sgt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.not := by show_hinv_mem_unary
instance : Rinst.Hinv Devm.memory Rinst.iszero := by show_hinv_mem_unary
instance : Rinst.Hinv Devm.memory Rinst.address := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.caller := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.callvalue := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.retdatasize := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.calldatasize := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.selfbalance := by show_hinv_mem_push

instance : Rinst.Hinv Devm.memory Rinst.pop := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;> simp [hp] at h1
  subst h1
  exact (Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas h2)).memory⟩

instance : Rinst.Hinv Devm.memory Rinst.gas := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact (Devm.pushBurn_of_burn_of_push (Devm.burn_of_chargeGas h1)
    (Devm.push_of_push h2)).memory⟩

instance {n} : Rinst.Hinv Devm.memory (Rinst.dup n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · exact (Devm.pushBurn_of_burn_of_push hb (Devm.push_of_push h2)).memory⟩

instance {n} : Rinst.Hinv Devm.memory (Rinst.swap n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    rw [hb.memory, ← eq]
    rfl⟩

instance : Rinst.Hinv Devm.memory Rinst.calldataload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  exact ((Devm.pop_of_pop h1).memory.trans
    (Devm.burn_of_chargeGas h2).memory).trans (Devm.push_of_push run₂).memory⟩

/-- `SLOAD` reads storage and touches nothing else.  Not covered by the routine
macros above because the cold/warm split makes it two shapes rather than one. -/
instance : Rinst.Hinv Devm.memory Rinst.sload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  refine (Devm.pop_of_pop h1).memory.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s₁.memory = d.memory →
      (chargeGas c d >>= fun y => Devm.push (Devm.getStorVal y sevm.currentTarget key) y)
        = .ok post → s₁.memory = post.memory by
    split at run₁
    · exact H s₁ gasWarmAccess rfl run₁
    · exact H (addAccessedStorageKey s₁ sevm.currentTarget key) gasColdSload rfl run₁
  intro d c hm run'
  rcases Except.bind_eq_ok run' with ⟨s₂, h2, run₂⟩
  exact (hm.trans (Devm.burn_of_chargeGas h2).memory).trans (Devm.push_of_push run₂).memory⟩

/-- `SSTORE` writes storage and touches nothing else.  The longest of these
proofs only because the instruction has the most intermediate states: the
access-list split, the refund counter, the gas charge and the dynamic assert
each produce one, and every one of them leaves `Devm.memory` alone. -/
instance : Rinst.Hinv Devm.memory Rinst.sstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have m3 : s₂.memory = s₃.memory := by
    injection h4 with eq
    split at eq <;> (injection eq with eq _; subst eq; rfl)
  have m4 : s₃.memory = s₄.memory := by
    injection h6 with eq; rw [← eq]; rfl
  injection h9 with eq
  rw [← eq]
  show pre.memory = s₅.memory
  exact ((((Devm.pop_of_pop h1).memory.trans (Devm.pop_of_pop h2).memory).trans m3).trans
    m4).trans (Devm.burn_of_chargeGas h7).memory⟩

/-! The two `Ninst` constructors that are not `reg`, so that `line_inv` carries
a memory image across a whole `Line` rather than stopping at the first `PUSH`.
Their `Devm.getBal` / `Devm.getStor` / `Devm.getCode` / `Devm.state` siblings
are above, beside the rest of the `Ninst.Hinv` API. -/

instance {x} : Ninst.Hinv Devm.memory (Ninst.pushB256 x) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).memory⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.memory (Ninst.push xs p) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).memory⟩

/-! ### What the permit approval tail does to logs and output

Ordinary scratch instructions preserve both fields.  `LOG` is intentionally
absent from the log instances: its exact append effect is exposed by
`of_run_log_val` / `of_logWith201_val` below.  These instances are the minimal
projection seam needed to carry that value-carrying observation across the
surrounding copy/hash/store instructions.  They live in an opt-in scope so
unrelated `line_inv` searches do not pay for these additional candidates. -/

namespace LogOutputHinv

syntax "show_hinv_logs_binary" : tactic
macro_rules
  | `(tactic| show_hinv_logs_binary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs)

syntax "show_hinv_output_binary" : tactic
macro_rules
  | `(tactic| show_hinv_output_binary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output)

syntax "show_hinv_logs_unary" : tactic
macro_rules
  | `(tactic| show_hinv_logs_unary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact (Devm.diffBurn_of_applyUnary run).choose_spec.logs)

syntax "show_hinv_output_unary" : tactic
macro_rules
  | `(tactic| show_hinv_output_unary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact (Devm.diffBurn_of_applyUnary run).choose_spec.output)

scoped instance : Rinst.Hinv Devm.logs Rinst.and := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.add := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.or := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.eq := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.gt := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.lt := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.shl := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.shr := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.iszero := by show_hinv_logs_unary
scoped instance : Rinst.Hinv Devm.logs Rinst.not := by show_hinv_logs_unary

scoped instance : Rinst.Hinv Devm.output Rinst.and := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.add := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.or := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.eq := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.gt := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.lt := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.shl := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.shr := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.iszero := by show_hinv_output_unary
scoped instance : Rinst.Hinv Devm.output Rinst.not := by show_hinv_output_unary

scoped instance {x} : Ninst.Hinv Devm.logs (Ninst.pushB256 x) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).logs⟩

scoped instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.logs (Ninst.push xs p) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).logs⟩

scoped instance {n} : Ninst.Hinv Devm.logs (Ninst.dup n) := ⟨by
  intro e s s' h
  rcases of_run_dup h with ⟨x, hx, hpb⟩
  exact hpb.logs⟩

scoped instance {n} : Ninst.Hinv Devm.output (Ninst.dup n) := ⟨by
  intro e s s' h
  rcases of_run_dup h with ⟨x, hx, hpb⟩
  exact hpb.output⟩

scoped instance {x} : Ninst.Hinv Devm.output (Ninst.pushB256 x) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).output⟩

scoped instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.output (Ninst.push xs p) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.address := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.address := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.caller := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.caller := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.pop := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;> simp [hp] at h1
  subst h1
  exact (Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas h2)).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.pop := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;> simp [hp] at h1
  subst h1
  exact (Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas h2)).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.gas := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact (Devm.burn_of_chargeGas h1).logs.trans
    (Devm.push_of_push h2).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.gas := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact (Devm.burn_of_chargeGas h1).output.trans
    (Devm.push_of_push h2).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.sload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hp := Devm.pop_of_pop h1
  split at run₁
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hp.logs.trans
      ((Devm.burn_of_chargeGas h2).logs.trans (Devm.push_of_push h3).logs)
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    have ha : s₁.logs =
        (addAccessedStorageKey s₁ sevm.currentTarget key).logs := rfl
    exact hp.logs.trans (ha.trans
      ((Devm.burn_of_chargeGas h2).logs.trans (Devm.push_of_push h3).logs))⟩

scoped instance : Rinst.Hinv Devm.output Rinst.sload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hp := Devm.pop_of_pop h1
  split at run₁
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hp.output.trans
      ((Devm.burn_of_chargeGas h2).output.trans (Devm.push_of_push h3).output)
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    have ha : s₁.output =
        (addAccessedStorageKey s₁ sevm.currentTarget key).output := rfl
    exact hp.output.trans (ha.trans
      ((Devm.burn_of_chargeGas h2).output.trans (Devm.push_of_push h3).output))⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.extcodesize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨adr, s₁⟩, h1, run₁⟩
  rw [Devm.popToAdr_def] at h1
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨word, d0⟩ <;>
    simp [hp] at h1
  rcases h1 with ⟨rfl, rfl⟩
  have hpop := Devm.pop_of_pop hp
  split at run₁
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hpop.logs.trans
      ((Devm.burn_of_chargeGas h2).logs.trans (Devm.push_of_push h3).logs)
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    have ha : d0.logs = (addAccessedAddress d0 word.toAdr).logs := rfl
    exact hpop.logs.trans (ha.trans
      ((Devm.burn_of_chargeGas h2).logs.trans (Devm.push_of_push h3).logs))⟩

scoped instance : Rinst.Hinv Devm.output Rinst.extcodesize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨adr, s₁⟩, h1, run₁⟩
  rw [Devm.popToAdr_def] at h1
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨word, d0⟩ <;>
    simp [hp] at h1
  rcases h1 with ⟨rfl, rfl⟩
  have hpop := Devm.pop_of_pop hp
  split at run₁
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hpop.output.trans
      ((Devm.burn_of_chargeGas h2).output.trans (Devm.push_of_push h3).output)
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    have ha : d0.output = (addAccessedAddress d0 word.toAdr).output := rfl
    exact hpop.output.trans (ha.trans
      ((Devm.burn_of_chargeGas h2).output.trans (Devm.push_of_push h3).output))⟩

scoped instance {n} : Rinst.Hinv Devm.logs (Rinst.swap n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    rw [hb.logs, ← eq]
    rfl⟩

scoped instance {n} : Rinst.Hinv Devm.output (Rinst.swap n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    rw [hb.output, ← eq]
    rfl⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.calldataload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  exact ((Devm.pop_of_pop h1).logs.trans
    (Devm.burn_of_chargeGas h2).logs).trans (Devm.push_of_push run₂).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.calldataload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  exact ((Devm.pop_of_pop h1).output.trans
    (Devm.burn_of_chargeGas h2).output).trans (Devm.push_of_push run₂).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.calldatacopy := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.logs
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.logs
  have hp3 := (Devm.pop_of_popToNat h3).choose_spec.logs
  have hb := (Devm.burn_of_chargeGas h4).logs
  injection h5 with eq
  rw [← eq]
  exact ((hp1.trans hp2).trans hp3).trans hb⟩

scoped instance : Rinst.Hinv Devm.output Rinst.calldatacopy := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.output
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.output
  have hp3 := (Devm.pop_of_popToNat h3).choose_spec.output
  have hb := (Devm.burn_of_chargeGas h4).output
  injection h5 with eq
  rw [← eq]
  exact ((hp1.trans hp2).trans hp3).trans hb⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.kec := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.logs
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.logs
  have hb := (Devm.burn_of_chargeGas h3).logs
  have hpush := (Devm.push_of_push run₃).logs
  exact ((hp1.trans hp2).trans hb).trans hpush⟩

scoped instance : Rinst.Hinv Devm.output Rinst.kec := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.output
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.output
  have hb := (Devm.burn_of_chargeGas h3).output
  have hpush := (Devm.push_of_push run₃).output
  exact ((hp1.trans hp2).trans hb).trans hpush⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.mstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨value, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, h4⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.logs
  have hp2 := (Devm.pop_of_pop h2).logs
  have hb := (Devm.burn_of_chargeGas h3).logs
  injection h4 with eq
  rw [← eq]
  exact (hp1.trans hp2).trans hb⟩

scoped instance : Rinst.Hinv Devm.output Rinst.mstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨value, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, h4⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.output
  have hp2 := (Devm.pop_of_pop h2).output
  have hb := (Devm.burn_of_chargeGas h3).output
  injection h4 with eq
  rw [← eq]
  exact (hp1.trans hp2).trans hb⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.sstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have l3 : s₂.logs = s₃.logs := by
    injection h4 with eq
    split at eq <;> (injection eq with eq _; subst eq; rfl)
  have l4 : s₃.logs = s₄.logs := by
    injection h6 with eq
    rw [← eq]
    rfl
  injection h9 with eq
  rw [← eq]
  exact ((((Devm.pop_of_pop h1).logs.trans (Devm.pop_of_pop h2).logs).trans
    l3).trans l4).trans (Devm.burn_of_chargeGas h7).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.sstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have o3 : s₂.output = s₃.output := by
    injection h4 with eq
    split at eq <;> (injection eq with eq _; subst eq; rfl)
  have o4 : s₃.output = s₄.output := by
    injection h6 with eq
    rw [← eq]
    rfl
  injection h9 with eq
  rw [← eq]
  exact ((((Devm.pop_of_pop h1).output.trans (Devm.pop_of_pop h2).output).trans
    o3).trans o4).trans (Devm.burn_of_chargeGas h7).output⟩

scoped instance {n} : Rinst.Hinv Devm.output (Rinst.log n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨_, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨_, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨_, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases hmem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [hmem] at run₅
  injection run₅ with eq
  have hm : s₄.output = s₅.output := by
    simp only [Devm.memRead] at hmem
    rcases hread : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [hread] at hmem
    injection hmem with _ hdevm
    rw [← hdevm]
    rfl
  rw [← eq]
  exact ((((p1.output.trans p2.output).trans p3.output).trans hb.output).trans hm)⟩

scoped instance : Linst.Hinv Devm.logs Devm.logs Linst.stop := by
  constructor
  intro e s r h
  injection h with h_eq
  subst h_eq
  rfl

/-- `RETURN` changes output but leaves the accumulated event log untouched. -/
scoped instance retLogs : Linst.Hinv Devm.logs Devm.logs Linst.ret := by
  constructor
  intro e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨⟨index, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨size, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat h1 with ⟨_, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨_, p2⟩
  have hb := Devm.burn_of_chargeGas h3
  rcases hmem : Devm.memRead s₃ index size with ⟨output, s₄⟩
  rw [hmem] at run₃
  injection run₃ with eq
  have hm : s₃.logs = s₄.logs := by
    simp only [Devm.memRead] at hmem
    rcases hread : s₃.memory.read index size with ⟨val, mem⟩
    rw [hread] at hmem
    injection hmem with _ hdevm
    rw [← hdevm]
    rfl
  rw [← eq]
  exact (((p1.logs.trans p2.logs).trans hb.logs).trans hm)

scoped instance : Linst.Hinv Devm.output Devm.output Linst.stop := by
  constructor
  intro e s r h
  injection h with h_eq
  subst h_eq
  rfl

end LogOutputHinv


/-! ### Dispatch reachability

The converse direction of `dispatchWith_inv`.  That lemma transfers a property
through the dispatcher precisely by never knowing which leaf ran; the theorems
here say which leaf runs, and sortedness — consumed for the first time in the
repository — is what supplies the selector→leaf link `dispatchWith_inv`'s
freely-quantified comparisons are deliberately blind to.

**Everything is hypothesis-position.**  A dispatcher run already in hand is
factored through the selector's entry; nothing here asserts that any run
exists, and no consumer may read `reach_of_dispatchWith` as "the selector is
present, therefore its function will be called" — that is a liveness claim and
is not available in this semantics.

The proofs reason from the abstract `sorted` hypothesis and never force a
signature word, so a concrete contract's `String.keccak` selectors stay
unevaluated; at instantiation, sortedness is supplied by the contract's
`decide +kernel` fact (`wethFuncs_sorted`, `fmintFuncs_sorted`). -/

/-! ## Nonpayable entry seam

`nonpayable` lives in `Blanc/CommonCore.lean` and is applied per endpoint by
more than one contract, so the lemmas that peel a successful run through it
live here rather than in any contract's module. -/

/-- A successful run through the nonpayable wrapper factors through the
endpoint body at a world-state- and memory-equivalent machine state, and only
with zero callvalue. The memory equation lets functional observations cross
the wrapper without assuming a pristine scratch area. -/
theorem run_body_of_run_nonpayable_frame
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ Func.Run fs sevm mid body r := by
  unfold nonpayable at run
  refine run_prepend_elim _ [callvalue, iszero] ?_ run
  intro s1 hline hbranch
  rcases Line.of_run_cons hline with ⟨s0, hcv, hline'⟩
  rcases Line.of_run_cons hline' with ⟨s1', hiz, hnil⟩
  cases hnil
  have hpv : [sevm.value] <<+ s0.stack :=
    prefix_of_push (of_run_callvalue hcv) nil_pref
  have hpflag : [sevm.value =? 0] <<+ s1.stack :=
    prefix_of_iszero hiz hpv
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hrev⟩ | ⟨w, s2, s3, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_rev
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpflag
    have hw : (sevm.value =? 0) = w :=
      pref_head_unique hpflag (pref_append [w] s2.stack)
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [hw]
      exact hnz
    have hv : sevm.value = 0 := by
      by_cases hv : sevm.value = 0
      · exact hv
      · simp [B256.eqCheck, hv] at hflag
    refine ⟨s3, hv, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)

/-- Compatibility projection of `run_body_of_run_nonpayable_frame` retaining
the original state-level API used by backing proofs. -/
theorem run_body_of_run_nonpayable
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      Func.Run fs sevm mid body r := by
  rcases run_body_of_run_nonpayable_frame run with
    ⟨mid, hv, hstate, _, hbody⟩
  exact ⟨mid, hv, hstate, hbody⟩

/-- A successful run through the shared nonpayable wrapper can only take the
endpoint arm, so the frame value is zero. -/
theorem value_eq_zero_of_run_nonpayable
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    sevm.value = 0 :=
  (run_body_of_run_nonpayable run).choose_spec.1

/-- Identify a popped word from a stack-prefix fact: popping from a stack whose
top is known pops exactly that word, and the prefix below it survives. -/
lemma popBurn_pref {w v : B256} {vs : Stack} {s s' : Devm}
    (h : Devm.PopBurn [w] s s') (h_pfx : v :: vs <<+ s.stack) :
    w = v ∧ (vs <<+ s'.stack) := by
  have h_stk := h.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at h_stk
  rcases h_pfx with ⟨t, h_t⟩
  rw [h_stk] at h_t
  simp only [Split, List.cons_append] at h_t
  injection h_t with h_head h_tail
  exact ⟨h_head, ⟨t, h_tail⟩⟩

/-- Reachability at a leaf: the selector equality test passes, so the run is in
the leaf's function, not the fallback.  The `s.state = s'.state` and
`s.memory = s'.memory` conjuncts are what the dispatcher's scratch instructions
preserve; gas is not tracked. -/
lemma reach_of_dispatchWith_leaf {sig w : B256} {f p : Func}
    {c : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack}
    (h_mem : (sig, f) ∈ [(w, p)])
    (h_pfx : sig :: ws <<+ s.stack) :
    Func.Run c e s (dispatchWith k (DispatchTree.leaf w p)) r →
    ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      Func.Run c e s' f r := by
  have h_eq : (sig, f) = (w, p) := List.mem_singleton.mp h_mem
  injection h_eq with h_sig h_f
  subst h_sig; subst h_f
  func_execute 2; intro h₂
  have h_pfx1 : (sig =? sig) :: ws <<+ s₁.stack := by generalize_line_prefix
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at h_pfx1
  rcases of_run_branch h₂ with ⟨s₂, h_pop, h_runf⟩ | ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_runf⟩
  · exact absurd (popBurn_pref h_pop h_pfx1).left B256.zero_ne_one
  · rcases popBurn_pref h_pop h_pfx1 with ⟨-, h_pfx2⟩
    refine ⟨s₃, ?_, ?_, ?_, h_runf⟩
    · rw [← h_burn.stack]; exact h_pfx2
    · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
        (h_pop.state.trans h_burn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
        (h_pop.memory.trans h_burn.memory)

/-- Dispatch reachability over `DispatchTree.build`: a dispatcher run whose
selector is an entry of the (sorted) list factors through that entry's
function.  `mem_of_mem_build`'s fuel bookkeeping recurs here — the length
bound keeps `build`'s entry-dropping fuel row unreachable, which is exactly
why reachability would be false without it. -/
theorem reach_of_dispatchWith_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {c : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (sig :: ws <<+ s.stack) →
      Func.Run c e s (dispatchWith k (DispatchTree.build n xs)) r →
      ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
        Func.Run c e s' f r := by
  intro n
  induction n with
  | zero =>
    intro xs sig f c k e s r ws h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatchWith_leaf h_mem h_pfx
    · intro _; exfalso; simp only [List.length_cons] at h_len; omega
  | succ n ih =>
    intro xs sig f c k e s r ws h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatchWith_leaf h_mem h_pfx
    · -- the fork: shared bookkeeping first, then the two branch arms
      simp only [List.length_cons] at h_len
      have h_take_len :
          (((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2)).length
            ≤ n + 1 := by
        simp only [List.length_take, List.length_cons]; omega
      have h_drop_len :
          (((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)).length
            ≤ n + 1 := by
        simp only [List.length_drop, List.length_cons]; omega
      obtain ⟨z, zs, h_drop⟩ :
          ∃ z zs, ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)
            = z :: zs := by
        rcases h_d : ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)
          with _ | ⟨z, zs⟩
        · exfalso
          have h_l := congrArg List.length h_d
          simp only [List.length_drop, List.length_cons, List.length_nil] at h_l
          omega
        · exact ⟨z, zs, rfl⟩
      have h_sorted_split : DispatchTree.sorted
          (((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) ++
           ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)) = true := by
        rw [List.take_append_drop]; exact h_sorted
      have h_sorted_take := DispatchTree.sorted_append_left h_sorted_split
      have h_sorted_drop := DispatchTree.sorted_append_right h_sorted_split
      have h_mem_split : (sig, f) ∈
          ((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) ∨
          (sig, f) ∈ ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2) := by
        apply List.mem_append.mp
        rw [List.take_append_drop]
        exact h_mem
      func_execute 3; intro h₂
      have h_pfx1 :
          (leftmostFsig (DispatchTree.build n
            (((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2))) >? sig)
            :: sig :: ws <<+ s₁.stack := by
        generalize_line_prefix
      rw [h_drop, DispatchTree.leftmostFsig_build] at h_pfx1
      rcases of_run_branch h₂ with ⟨s₂, h_pop, h_run'⟩ | ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_run'⟩
      · -- comparison word 0 : `¬ sig < z.fst`, the run went right; so is the selector
        rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
        have h_le : z.fst ≤ sig := by
          rw [← B256.not_lt]; intro h_lt
          have h_gt : z.fst > sig := h_lt
          rw [B256.gtCheck, if_pos h_gt] at h_flag
          exact B256.zero_ne_one h_flag
        have h_mem_drop : (sig, f) ∈
            ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2) := by
          rcases h_mem_split with h_in | h_in
          · exfalso
            have h_z : z ∈ ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2) := by
              rw [h_drop]; exact List.mem_cons_self ..
            have h_lt := DispatchTree.fst_lt_of_sorted_append h_sorted_split h_in h_z
            have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
            have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
            omega
          · exact h_in
        rcases ih h_sorted_drop h_drop_len h_mem_drop h_pfx2 h_run'
          with ⟨s', h_s', h_st, h_mm, h_rf⟩
        refine ⟨s', h_s', ?_, ?_, h_rf⟩
        · exact (Line.of_inv Devm.state (by line_inv) h₁).trans (h_pop.state.trans h_st)
        · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans (h_pop.memory.trans h_mm)
      · -- comparison word nonzero : `sig < z.fst`, the run went left; so is the selector
        rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
        have h_lt : sig < z.fst := by
          by_contra h_nlt
          rw [B256.gtCheck, if_neg (fun h_gt => h_nlt h_gt)] at h_flag
          exact h_ne h_flag
        have h_mem_take : (sig, f) ∈
            ((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) := by
          rcases h_mem_split with h_in | h_in
          · exact h_in
          · exfalso
            rw [h_drop] at h_in
            have h_sorted_zzs : DispatchTree.sorted (z :: zs) = true := by
              rw [← h_drop]; exact h_sorted_drop
            have h_le := DispatchTree.fst_le_of_sorted_mem h_sorted_zzs h_in
            have h1 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
            have h2 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
            omega
        rw [h_burn.stack] at h_pfx2
        rcases ih h_sorted_take h_take_len h_mem_take h_pfx2 h_run'
          with ⟨s', h_s', h_st, h_mm, h_rf⟩
        refine ⟨s', h_s', ?_, ?_, h_rf⟩
        · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
            (h_pop.state.trans (h_burn.state.trans h_st))
        · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
            (h_pop.memory.trans (h_burn.memory.trans h_mm))

/-- **Dispatch reachability.**  A `dispatchWith` run over a sorted function
list, with selector `sig` on top of the stack at dispatcher entry, factors
through the function `sig` is paired with: the run reached `f`'s body in some
state `s'` that keeps the stack below the selector and the whole world state.

This is the converse of what `dispatchWith_inv` consumes and the first theorem
for which `DispatchTree.sorted` is load-bearing: `sound_of_dispatch` dropped
sortedness because a misordered list cannot make the dispatcher *unsound* — it
makes an entry unreachable, which is precisely the defect this theorem rules
out.  The run is a hypothesis: this factors an execution already in hand and
asserts nothing about whether one exists.

Memory is carried too (`s.memory = s'.memory`): the dispatcher's scratch
instructions are memory-silent, so a caller that knows what the frame's memory
holds on entry still knows it at the entry to the selected function.  That is
what lets a frame-freshness premise be stated where it belongs — at the frame's
own initial state — rather than at an intermediate state no caller can name. -/
theorem reach_of_dispatchWith {funcs : List (B256 × Func)} {sig : B256} {f : Func}
    {c : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack}
    (h_sorted : DispatchTree.sorted funcs = true)
    (h_mem : (sig, f) ∈ funcs)
    (h_pfx : sig :: ws <<+ s.stack)
    (h_run : Func.Run c e s (dispatchWith k (DispatchTree.ofSorted funcs)) r) :
    ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      Func.Run c e s' f r :=
  reach_of_dispatchWith_build h_sorted (Nat.le_succ _) h_mem h_pfx h_run

/-! ### Dispatch reachability with the event-log frame

Functional contract theorems need the same selected-leaf factorization as
`reach_of_dispatchWith`, but must also relate events emitted by the selected
body to the public frame's entry log.  These additive companions carry that
projection through the dispatcher while preserving the original API above.
The extra instruction instances are opt-in so unrelated invariant searches do
not pay for them. -/

section DispatchLogFrame

open scoped LogOutputHinv

/-! The entry route is `fsig +++ dispatch`, so the same log/output projection
a functional theorem carries through the dispatcher must first be carried
through `fsig`.  `prefix_of_fsig` above says which word the selector prefix
leaves on the stack; these two say what it leaves the event log and the output
buffer.  Both are pure `Line.Run` frames over the four instructions of
`cdl 0 ++ shiftRight 224`, and neither mentions a contract. -/

/-- `fsig` emits no event. -/
lemma fsig_logs {e : Sevm} {s t : Devm}
    (run : Line.Run e s fsig t) : s.logs = t.logs := by
  unfold fsig cdl shiftRight at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, hnil⟩
  cases hnil
  have hshr : s3.logs = t.logs := by
    rcases of_run_reg q4 with ⟨pc, hrun⟩
    simp only [Rinst.run, Rinst.runCore] at hrun
    exact (Devm.diffBurn_of_applyBinary hrun).choose_spec.choose_spec.logs
  exact (of_run_pushB256 q1).logs.trans
    ((Ninst.Hinv.inv (f := Devm.logs) q2).trans
      ((of_run_pushB256 q3).logs.trans hshr))

/-- `fsig` writes no output. -/
lemma fsig_output {e : Sevm} {s t : Devm}
    (run : Line.Run e s fsig t) : s.output = t.output := by
  unfold fsig cdl shiftRight at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, hnil⟩
  cases hnil
  have hshr : s3.output = t.output := by
    rcases of_run_reg q4 with ⟨pc, hrun⟩
    simp only [Rinst.run, Rinst.runCore] at hrun
    exact (Devm.diffBurn_of_applyBinary hrun).choose_spec.choose_spec.output
  exact (of_run_pushB256 q1).output.trans
    ((Ninst.Hinv.inv (f := Devm.output) q2).trans
      ((of_run_pushB256 q3).output.trans hshr))

lemma reach_of_dispatchWith_leaf_logs {sig w : B256} {f p : Func}
    {c : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack}
    (h_mem : (sig, f) ∈ [(w, p)])
    (h_pfx : sig :: ws <<+ s.stack) :
    Func.Run c e s (dispatchWith k (DispatchTree.leaf w p)) r →
    ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      s.logs = s'.logs ∧ s.output = s'.output ∧ Func.Run c e s' f r := by
  have h_eq : (sig, f) = (w, p) := List.mem_singleton.mp h_mem
  injection h_eq with h_sig h_f
  subst h_sig; subst h_f
  func_execute 2; intro h₂
  have h_pfx1 : (sig =? sig) :: ws <<+ s₁.stack := by generalize_line_prefix
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at h_pfx1
  rcases of_run_branch h₂ with ⟨s₂, h_pop, h_runf⟩ |
      ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_runf⟩
  · exact absurd (popBurn_pref h_pop h_pfx1).left B256.zero_ne_one
  · rcases popBurn_pref h_pop h_pfx1 with ⟨-, h_pfx2⟩
    refine ⟨s₃, ?_, ?_, ?_, ?_, ?_, h_runf⟩
    · rw [← h_burn.stack]; exact h_pfx2
    · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
        (h_pop.state.trans h_burn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
        (h_pop.memory.trans h_burn.memory)
    · exact (Line.of_inv Devm.logs (by line_inv) h₁).trans
        (h_pop.logs.trans h_burn.logs)
    · exact (Line.of_inv Devm.output (by line_inv) h₁).trans
        (h_pop.output.trans h_burn.output)

theorem reach_of_dispatchWith_build_logs :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {c : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (sig :: ws <<+ s.stack) →
      Func.Run c e s (dispatchWith k (DispatchTree.build n xs)) r →
      ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
        s.logs = s'.logs ∧ s.output = s'.output ∧
          Func.Run c e s' f r := by
  intro n
  induction n with
  | zero =>
    intro xs sig f c k e s r ws h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatchWith_leaf_logs h_mem h_pfx
    · intro _; exfalso; simp only [List.length_cons] at h_len; omega
  | succ n ih =>
    intro xs sig f c k e s r ws h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatchWith_leaf_logs h_mem h_pfx
    · simp only [List.length_cons] at h_len
      have h_take_len :
          (((w, p) :: y :: ys).take
            ((((w, p) :: y :: ys).length + 1) / 2)).length ≤ n + 1 := by
        simp only [List.length_take, List.length_cons]; omega
      have h_drop_len :
          (((w, p) :: y :: ys).drop
            ((((w, p) :: y :: ys).length + 1) / 2)).length ≤ n + 1 := by
        simp only [List.length_drop, List.length_cons]; omega
      obtain ⟨z, zs, h_drop⟩ :
          ∃ z zs, ((w, p) :: y :: ys).drop
              ((((w, p) :: y :: ys).length + 1) / 2) = z :: zs := by
        rcases h_d : ((w, p) :: y :: ys).drop
            ((((w, p) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
        · exfalso
          have h_l := congrArg List.length h_d
          simp only [List.length_drop, List.length_cons, List.length_nil] at h_l
          omega
        · exact ⟨z, zs, rfl⟩
      have h_sorted_split : DispatchTree.sorted
          (((w, p) :: y :: ys).take
              ((((w, p) :: y :: ys).length + 1) / 2) ++
           ((w, p) :: y :: ys).drop
              ((((w, p) :: y :: ys).length + 1) / 2)) = true := by
        rw [List.take_append_drop]; exact h_sorted
      have h_sorted_take := DispatchTree.sorted_append_left h_sorted_split
      have h_sorted_drop := DispatchTree.sorted_append_right h_sorted_split
      have h_mem_split : (sig, f) ∈
          ((w, p) :: y :: ys).take
              ((((w, p) :: y :: ys).length + 1) / 2) ∨
          (sig, f) ∈ ((w, p) :: y :: ys).drop
              ((((w, p) :: y :: ys).length + 1) / 2) := by
        apply List.mem_append.mp
        rw [List.take_append_drop]
        exact h_mem
      func_execute 3; intro h₂
      have h_pfx1 :
          (leftmostFsig (DispatchTree.build n
            (((w, p) :: y :: ys).drop
              ((((w, p) :: y :: ys).length + 1) / 2))) >? sig) ::
            sig :: ws <<+ s₁.stack := by
        generalize_line_prefix
      rw [h_drop, DispatchTree.leftmostFsig_build] at h_pfx1
      rcases of_run_branch h₂ with ⟨s₂, h_pop, h_run'⟩ |
          ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_run'⟩
      · rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
        have h_le : z.fst ≤ sig := by
          rw [← B256.not_lt]; intro h_lt
          have h_gt : z.fst > sig := h_lt
          rw [B256.gtCheck, if_pos h_gt] at h_flag
          exact B256.zero_ne_one h_flag
        have h_mem_drop : (sig, f) ∈
            ((w, p) :: y :: ys).drop
                ((((w, p) :: y :: ys).length + 1) / 2) := by
          rcases h_mem_split with h_in | h_in
          · exfalso
            have h_z : z ∈ ((w, p) :: y :: ys).drop
                ((((w, p) :: y :: ys).length + 1) / 2) := by
              rw [h_drop]; exact List.mem_cons_self ..
            have h_lt := DispatchTree.fst_lt_of_sorted_append
              h_sorted_split h_in h_z
            have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
            have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
            omega
          · exact h_in
        rcases ih h_sorted_drop h_drop_len h_mem_drop h_pfx2 h_run' with
          ⟨s', h_s', h_st, h_mm, h_logs, h_output, h_rf⟩
        refine ⟨s', h_s', ?_, ?_, ?_, ?_, h_rf⟩
        · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
            (h_pop.state.trans h_st)
        · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
            (h_pop.memory.trans h_mm)
        · exact (Line.of_inv Devm.logs (by line_inv) h₁).trans
            (h_pop.logs.trans h_logs)
        · exact (Line.of_inv Devm.output (by line_inv) h₁).trans
            (h_pop.output.trans h_output)
      · rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
        have h_lt : sig < z.fst := by
          by_contra h_nlt
          rw [B256.gtCheck, if_neg (fun h_gt => h_nlt h_gt)] at h_flag
          exact h_ne h_flag
        have h_mem_take : (sig, f) ∈
            ((w, p) :: y :: ys).take
                ((((w, p) :: y :: ys).length + 1) / 2) := by
          rcases h_mem_split with h_in | h_in
          · exact h_in
          · exfalso
            rw [h_drop] at h_in
            have h_sorted_zzs : DispatchTree.sorted (z :: zs) = true := by
              rw [← h_drop]; exact h_sorted_drop
            have h_le := DispatchTree.fst_le_of_sorted_mem h_sorted_zzs h_in
            have h1 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
            have h2 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
            omega
        rw [h_burn.stack] at h_pfx2
        rcases ih h_sorted_take h_take_len h_mem_take h_pfx2 h_run' with
          ⟨s', h_s', h_st, h_mm, h_logs, h_output, h_rf⟩
        refine ⟨s', h_s', ?_, ?_, ?_, ?_, h_rf⟩
        · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
            (h_pop.state.trans (h_burn.state.trans h_st))
        · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
            (h_pop.memory.trans (h_burn.memory.trans h_mm))
        · exact (Line.of_inv Devm.logs (by line_inv) h₁).trans
            (h_pop.logs.trans (h_burn.logs.trans h_logs))
        · exact (Line.of_inv Devm.output (by line_inv) h₁).trans
            (h_pop.output.trans (h_burn.output.trans h_output))

/-- `reach_of_dispatchWith` with the dispatcher-entry log carried to the
selected body.  The body may append logs afterward; this theorem only states
that dispatch itself is log-silent. -/
theorem reach_of_dispatchWith_logs
    {funcs : List (B256 × Func)} {sig : B256} {f : Func}
    {c : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack}
    (h_sorted : DispatchTree.sorted funcs = true)
    (h_mem : (sig, f) ∈ funcs)
    (h_pfx : sig :: ws <<+ s.stack)
    (h_run : Func.Run c e s (dispatchWith k (DispatchTree.ofSorted funcs)) r) :
    ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      s.logs = s'.logs ∧ s.output = s'.output ∧
        Func.Run c e s' f r :=
  reach_of_dispatchWith_build_logs h_sorted (Nat.le_succ _) h_mem h_pfx h_run

end DispatchLogFrame


/-! ## §1 AdrSet non-membership helpers -/

namespace AdrSet

theorem not_mem_insert {a b : Adr} {s : AdrSet} (hne : a ≠ b) (hs : a ∉ s) :
    a ∉ s.insert b := by
  simp only [Std.HashSet.mem_insert, not_or]
  exact ⟨by simpa using Ne.symm hne, hs⟩

theorem not_mem_union {a : Adr} {m₁ m₂ : AdrSet} (h₁ : a ∉ m₁) (h₂ : a ∉ m₂) :
    a ∉ m₁.union m₂ := by
  intro h
  have hm : a ∈ m₁ ∨ a ∈ m₂ := Std.HashSet.mem_union_iff.mp h
  exact hm.elim h₁ h₂

theorem not_mem_empty {a : Adr} {c : Nat} :
    a ∉ (Std.HashSet.emptyWithCapacity c : AdrSet) := by
  simp

end AdrSet

/-! ## §2 The NoDel invariant -/

-- rfl-bridge between the Devm-level and State-level code projections.
lemma Devm.getCode_state (d : Devm) (a : Adr) :
    d.getCode a = d.state.getCode a := rfl

-- The frame-level invariant. The `code` conjunct is the fuel for the
-- CREATE collision guards; it is transported by the PROVED getCode ladder,
-- never re-proved here.
structure Devm.NoDel (wa : Adr) (d : Devm) : Prop where
  (atd  : wa ∉ d.accountsToDelete)
  (ca   : wa ∉ d.createdAccounts)
  (code : (d.getCode wa).toList ≠ [])

-- The message-level invariant (a fresh frame starts with atd = ∅,
-- ca = msg.benv.createdAccounts, state = msg.benv.state; see initDevm,
-- jaune Execution.lean:2657).
structure Msg.NoDel (wa : Adr) (msg : Msg) : Prop where
  (ca   : wa ∉ msg.benv.createdAccounts)
  (code : (msg.benv.state.getCode wa).toList ≠ [])

-- Result-level invariants: error payloads carry live atd/ca (handleError
-- can resurrect them into ok results), so they must be covered.
def Execution.NoDel (wa : Adr) : Execution → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, d⟩ => Devm.NoDel wa d

-- Msg-level results (`processMessage`-shaped): the error payload carries
-- only createdAccounts + state (no atd; consumers merge it via
-- liftToExecution, keeping the parent's atd).
def MsgResult.NoDel (wa : Adr) :
    Except (EvmError × State × AdrSet × Tra) Devm → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, st, ca, _⟩ => wa ∉ ca ∧ (st.getCode wa).toList ≠ []

-- The sub-execution oracle invariant threaded through the Exec induction
-- (result-shaped like Xlot.InvGetCode, Common.lean:4076; the former
-- Xlot.InvNof mirror in Solvent.lean was replaced by Exec.balance_effect).
def Xlot.InvNoDel (wa : Adr) : Xlot → Prop
  | .none => True
  | .some ⟨evm_, exn_⟩ => Devm.NoDel wa evm_.dyna → Execution.NoDel wa exn_

/-! ## §3 Proved transports -/

-- Transport NoDel across a step that moves neither set nor wa's code.
lemma Devm.NoDel.of_eqs {wa : Adr} {d d' : Devm}
    (hs : Devm.delSets d = Devm.delSets d') (hc : d.getCode wa = d'.getCode wa)
    (h : Devm.NoDel wa d) : Devm.NoDel wa d' := by
  have h1 : d.accountsToDelete = d'.accountsToDelete := congrArg Prod.fst hs
  have h2 : d.createdAccounts = d'.createdAccounts := congrArg Prod.snd hs
  exact ⟨h1 ▸ h.atd, h2 ▸ h.ca, hc ▸ h.code⟩

-- A fresh frame satisfies NoDel (initDevm: atd := ∅, ca := benv.ca).
lemma Msg.NoDel.initDevm {wa : Adr} {msg : Msg}
    (h : Msg.NoDel wa msg) : Devm.NoDel wa (initDevm msg) :=
  ⟨AdrSet.not_mem_empty, h.ca, h.code⟩

-- Rollback keeps atd/ca and installs the given state.
lemma Devm.NoDel.rollback {wa : Adr} {d : Devm} {st : State} {tra : Tra}
    (h_atd : wa ∉ d.accountsToDelete) (h_ca : wa ∉ d.createdAccounts)
    (h_code : (st.getCode wa).toList ≠ []) :
    Devm.NoDel wa (d.rollback st tra) :=
  ⟨h_atd, h_ca, h_code⟩

-- handleError shuffles error payloads into ok results without touching
-- the sets (jaune Execution.lean:2692-2701).
lemma handleError_noDel {wa : Adr} {exn : Execution}
    (h : Execution.NoDel wa exn) :
    MsgResult.NoDel wa (executeCode.handleError exn) := by
  cases exn with
  | ok d => exact h
  | error p =>
    rcases p with ⟨err, d⟩
    have hd : Devm.NoDel wa d := h
    cases err <;>
      first
        | exact ⟨hd.atd, hd.ca, hd.code⟩
        | exact ⟨hd.ca, hd.code⟩

/-! ## §4 Plumbing -/

-- The create-guard bridge: an address whose account has size-0 code cannot be the code-bearing wa.
lemma ne_wa_of_code_size_zero {st : State} {wa b : Adr}
    (hwa : (st.getCode wa).toList ≠ []) (hb : (st.get b).code.size = 0) :
    b ≠ wa := by
  intro h
  subst h
  have h_empty : (st.get b).code.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  unfold State.getCode at hwa
  rw [h_empty] at hwa
  exact hwa rfl

-- Same bridge via the collision predicate used by `processMessageCall.create`.
lemma ne_wa_of_not_hasCodeOrNonce {st : State} {wa ct : Adr}
    (hwa : (st.getCode wa).toList ≠ [])
    (h : accountHasCodeOrNonce st ct = false) : ct ≠ wa := by
  intro heq
  subst heq
  unfold accountHasCodeOrNonce at h
  rw [Bool.or_eq_false_iff] at h
  have h_empty_not := h.2
  have h_empty : (st.getCode ct).isEmpty = true := by
    simp at h_empty_not
    exact h_empty_not
  have hb : (st.getCode ct).size = 0 := by
    unfold ByteArray.isEmpty at h_empty
    simp at h_empty
    simpa using congrArg ByteArray.size h_empty
  have h_empty_list : (st.getCode ct).toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  rw [h_empty_list] at hwa
  exact hwa rfl

-- The create-seeding step: wa ∉ msg.benv.createdAccounts and code is untouched.
lemma Msg.NoDel.processCreateMessage_msg {wa : Adr} {msg : Msg}
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (processCreateMessage.msg msg) := by
  rcases h with ⟨hca, hcode⟩
  refine ⟨?_, ?_⟩
  · show wa ∉ msg.benv.createdAccounts.insert msg.currentTarget
    exact AdrSet.not_mem_insert (Ne.symm h_ct) hca
  · show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).getCode wa).toList ≠ []
    have h_get : ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa = msg.benv.state.get wa := by
      dsimp only [State.incrNonce, State.setStor]
      rw [State.get_set_ne _ h_ct, State.get_set_ne _ h_ct]
    show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa).code.toList ≠ []
    rw [h_get]
    exact hcode

-- Precompiles never touch the sets or code.
lemma executePrecomp_noDel {wa : Adr} {evm : Evm} {adr : Adr} {exn : Execution}
    (h_ex : executePrecomp evm adr = exn)
    (h : Devm.NoDel wa evm.dyna) : Execution.NoDel wa exn := by
  unfold executePrecomp at h_ex
  revert h_ex
  generalize h_res : precompileRun evm adr = res
  intro h_ex
  subst h_ex
  cases res
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h

/-! ## §5 Instruction level -/

-- Helper lemmas for the EVM instructions delSets preservation.
lemma liftMach_delSets_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    Devm.delSets d' = Devm.delSets d := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp [hc] at h
  | ok out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    rfl

lemma liftMach_delSets_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : EvmError × Devm} (h : liftMach core d = .error err) :
    Devm.delSets err.2 = Devm.delSets d := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | ok out => simp [hc] at h

lemma liftMachExecution_delSets_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    Devm.delSets d' = Devm.delSets d := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_delSets_of_ok heq

lemma liftMachExecution_delSets_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : EvmError × Devm} (h : liftMachExecution core d = .error err) :
    Devm.delSets err.2 = Devm.delSets d := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_delSets_of_error heq
  · cases h

lemma Devm.pop_delSets_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  simp only [Devm.pop_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_eq {v devm devm'} (h : Devm.push v devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_ok (core := Mach.push v) h

lemma Devm.popToAdr_delSets_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMach_delSets_of_ok (core := Mach.popToAdr) h

lemma Devm.popToNat_delSets_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMach_delSets_of_ok (core := Mach.popToNat) h

lemma Rinst.inv_delSets {r : Rinst} : Rinst.Inv Devm.delSets r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact Devm.InstructionFrame.delSets hf

lemma chargeGas_delSets_err {cost devm err} (h : chargeGas cost devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_err {v devm err} (h : Devm.push v devm = Except.error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_error (core := Mach.push v) h

lemma Devm.popToAdr_delSets_err {devm err} (h : Devm.popToAdr devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMach_delSets_of_error (core := Mach.popToAdr) h

-- Rinst execution preserves delSets on error results.
lemma Rinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {r : Rinst}
    {err : EvmError} {devm' : Devm}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .error ⟨err, devm'⟩) :
    Devm.delSets devm' = Devm.delSets devm := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by change devm.accountsToDelete = devm'.accountsToDelete; exact hf.accountsToDelete) (by change devm.createdAccounts = devm'.createdAccounts; exact hf.createdAccounts)).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by change devm.accountsToDelete = devm'.accountsToDelete; exact hf.accountsToDelete) (by change devm.createdAccounts = devm'.createdAccounts; exact hf.createdAccounts)).symm
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf
    exact (Devm.InstructionFrame.delSets hf).symm

lemma Jinst.inv_delSets {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc' : Nat} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    Devm.delSets devm' = Devm.delSets devm := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

lemma Jinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {err : EvmError} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)) :
    Devm.delSets devm' = Devm.delSets devm := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

-- Halting/terminal instructions (Linst) preserve NoDel.
lemma Linst.dest_preserves_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {exn : Execution} (run : Linst.Run sevm devm .dest exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : devm.popToAdr <;> dsimp
  case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_err h1).symm (Devm.popToAdr_getCode_err h1 wa).symm h
  case ok res1 =>
    have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode wa = res1.2.getCode wa := by
      split
      · exact addAccessedAddress_getCode
      · rfl
    have h_acc_ds : Devm.delSets
        (if res1.1 ∉ res1.2.accessedAddresses then
          (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess)
        else (res1.2, gasSelfDestruct)).1 = Devm.delSets res1.2 := by
      split
      · rfl
      · rfl
    cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_err h2).symm (chargeGas_getCode_err h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
    case ok res2 =>
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run; rw [← run]
        dsimp [assertDynamic, Except.assert] at h3
        split at h3
        · contradiction
        · simp only [Except.error.injEq] at h3; subst h3
          exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run; rw [← run]
          exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
        case some res3 =>
          have hd : Devm.NoDel wa res2 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
          have h_sub : res3.getCode wa = res2.getCode wa := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none =>
              rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              change st.getCode wa = res2.getCode wa
              exact State.subBal_getCode h_st
          have h_sub_ds : Devm.delSets res3 = Devm.delSets res2 := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none => rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              rfl
          have hd3 : Devm.NoDel wa res3 := Devm.NoDel.of_eqs h_sub_ds.symm h_sub.symm hd
          by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos]
            intro run; rw [← run]
            have h_ca_eq : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts = res3.createdAccounts := rfl
            have h_ca : sevm.currentTarget ∈ res3.createdAccounts := h_ca_eq ▸ h_if
            have h_ne : sevm.currentTarget ≠ wa := by
              intro heq; rw [heq] at h_ca
              exact hd3.ca h_ca
            constructor
            · exact AdrSet.not_mem_insert (Ne.symm h_ne) hd3.atd
            · exact hd3.ca
            · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
              have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode wa = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa := by
                dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
              have h_code : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode wa = res3.getCode wa :=
                h_set.trans h_add
              rw [h_code]; exact hd3.code
          · simp only [h_if]
            intro run; rw [← run]
            constructor
            · exact hd3.atd
            · exact hd3.ca
            · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
              rw [h_add]; exact hd3.code

theorem Linst.run_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {l : Linst} {exn : Execution} (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · exact Linst.dest_preserves_noDel run h
  · have hf := Linst.run_instructionFrame sevm devm l h_not_dest
    rw [run] at hf
    cases exn <;>
      exact Devm.NoDel.of_eqs (Devm.InstructionFrame.delSets hf) (hf.getCode wa) h

lemma Linst.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution}
    (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  exact Linst.run_noDel run h

lemma Msg.NoDel.benvAfterTransfer_err {wa : Adr} {msg : Msg}
    {x : EvmError × State × AdrSet × Tra}
    (h_run : msg.benvAfterTransfer = .error x)
    (h : Msg.NoDel wa msg) : wa ∉ x.2.2.1 ∧ (x.2.1.getCode wa).toList ≠ [] := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_pos h_stv] at h_run
    cases h_sub : msg.benv.subBal msg.caller msg.value
    · rw [h_sub] at h_run
      simp only [Except.error.injEq, Option.toExcept, Except.bind, bind] at h_run
      subst h_run
      exact ⟨h.ca, h.code⟩
    · rw [h_sub] at h_run
      dsimp [Option.toExcept] at h_run
      contradiction
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    contradiction

lemma chargeCodeGas_delSets_ok {rules : ForkRules} {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas rules d = .ok d') :
    Devm.delSets d' = Devm.delSets d := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h
  · rcases Except.bind_eq_ok h with ⟨d1, h_charge, h_rest⟩
    split_ifs at h_rest
    cases h_rest
    exact chargeGas_delSets_eq h_charge

lemma chargeCodeGas_delSets_err {rules : ForkRules} {d d' : Devm} {err : EvmError}
    (h : processCreateMessage.chargeCodeGas rules d = .error ⟨err, d'⟩) :
    Devm.delSets d' = Devm.delSets d := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h; rfl
  · rcases hcg : chargeGas _ d with ⟨e, dd⟩ | dd
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases h
      exact chargeGas_delSets_err hcg
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      split_ifs at h
      cases h; exact chargeGas_delSets_eq hcg

lemma Devm.push_noDel {wa : Adr} {x : B256} {d : Devm} {exn : Execution}
    (heq : Devm.push x d = exn) (h : Devm.NoDel wa d) : Execution.NoDel wa exn := by
  subst heq
  cases hp : Devm.push x d with
  | error err =>
    have hd := Devm.push_delSets_err hp
    refine ⟨?_, ?_, (Devm.push_getCode_err hp wa) ▸ h.code⟩
    · rw [show err.2.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show err.2.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca
  | ok d' =>
    have hd := Devm.push_delSets_eq hp
    refine ⟨?_, ?_, (Devm.push_getCode_eq hp wa) ▸ h.code⟩
    · rw [show d'.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show d'.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca

lemma incorporateChildOnError_noDel {wa : Adr} {parent child : Devm} {rd : Bytes}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnError parent child rd) :=
  ⟨hp_atd, hc.ca, hc.code⟩

lemma incorporateChildOnSuccess_noDel {wa : Adr} {parent child : Devm} {rd : Bytes}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnSuccess parent child rd) :=
  ⟨AdrSet.not_mem_union hp_atd hc.atd, hc.ca, hc.code⟩

lemma Devm.pop_err_snd {d : Devm} {x : EvmError × Devm}
    (h : Devm.pop d = .error x) : x.2 = d := by
  simp only [Devm.pop_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Devm.popToAdr_err_snd {d : Devm} {x : EvmError × Devm}
    (h : Devm.popToAdr d = .error x) : x.2 = d := by
  rw [Devm.popToAdr_def] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp)

lemma chargeGas_err_snd {cost : Nat} {d : Devm} {x : EvmError × Devm}
    (h : chargeGas cost d = .error x) : x.2 = d := by
  simp only [chargeGas_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Except.assert_err_snd {p : Prop} [Decidable p] {d : Devm} {s : EvmError}
    {x : EvmError × Devm} (h : Except.assert p (⟨s, d⟩ : EvmError × Devm) = .error x) :
    x.2 = d := by
  simp only [Except.assert] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; exact (congrArg Prod.snd h).symm

lemma Devm.NoDel.pop {wa : Adr} {d d' : Devm} {v : B256}
    (hd : Devm.NoDel wa d) (h : Devm.pop d = .ok ⟨v, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.pop_delSets_eq h).symm (Devm.pop_getCode h).symm

lemma Devm.NoDel.popToNat {wa : Adr} {d d' : Devm} {n : Nat}
    (hd : Devm.NoDel wa d) (h : Devm.popToNat d = .ok ⟨n, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToNat_delSets_eq h).symm (Devm.popToNat_getCode h).symm

lemma Devm.NoDel.popToAdr {wa : Adr} {d d' : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) (h : Devm.popToAdr d = .ok ⟨a, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToAdr_delSets_eq h).symm (Devm.popToAdr_getCode h).symm

lemma Devm.NoDel.chargeGas {wa : Adr} {d d' : Devm} {cost : Nat}
    (hd : Devm.NoDel wa d) (h : chargeGas cost d = .ok d') : Devm.NoDel wa d' :=
  hd.of_eqs (chargeGas_delSets_eq h).symm (chargeGas_getCode h).symm

lemma Devm.NoDel.memExtends {wa : Adr} {d : Devm} {ranges : List (Nat × Nat)}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (d.memExtends ranges) := by
  refine hd.of_eqs ?_ Devm.memExtends_getCode.symm
  rfl

lemma Devm.NoDel.addAccessedAddress {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (Jaune.addAccessedAddress d a) := by
  refine hd.of_eqs ?_ addAccessedAddress_getCode.symm
  rfl

def Benv.EquivForDelegation (b1 b2 : Benv) : Prop :=
  b2.createdAccounts = b1.createdAccounts ∧
  ∀ a, (b1.state.getCode a).toList ≠ [] →
    ¬ isValidDelegation (b1.state.getCode a) →
    b2.state.getCode a = b1.state.getCode a

lemma Benv.EquivForDelegation_refl (b : Benv) : Benv.EquivForDelegation b b := by
  refine ⟨rfl, fun _ _ _ => rfl⟩

lemma Benv.EquivForDelegation_trans {b1 b2 b3 : Benv} (h12 : Benv.EquivForDelegation b1 b2) (h23 : Benv.EquivForDelegation b2 b3) :
    Benv.EquivForDelegation b1 b3 := by
  rcases h12 with ⟨h1c, h1code⟩
  rcases h23 with ⟨h2c, h2code⟩
  refine ⟨by rw [h2c, h1c], fun a ha hnd => ?_⟩
  have h1 := h1code a ha hnd
  have ha2' : (b2.state.getCode a).toList ≠ [] := by
    rw [h1]
    exact ha
  have hnd2 : ¬ isValidDelegation (b2.state.getCode a) := by
    rw [h1]
    exact hnd
  rw [h2code a ha2' hnd2, h1]

lemma Msg.NoDel.benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_run : msg.benvAfterTransfer = .ok benv)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (msg.withBenv benv) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [h_stv] at h_run
    simp only [if_true] at h_run
    unfold Benv.subBal at h_run
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      contradiction
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      injection h_run with hB
      have hBc : benv.createdAccounts = msg.benv.createdAccounts := by
        rw [← hB]; rfl
      have h_code_add : benv.state.getCode wa = st_mid.getCode wa := by
        have hBs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
          rw [← hB]; rfl
        rw [hBs]; exact State.addBal_getCode st_mid msg.currentTarget wa msg.value
      have h_code_sub : st_mid.getCode wa = msg.benv.state.getCode wa := by
        exact State.subBal_getCode h_sub
      have h_code : ((msg.withBenv benv).benv.state.getCode wa).toList ≠ [] := by
        change (benv.state.getCode wa).toList ≠ []
        rw [h_code_add, h_code_sub]
        exact h.code
      exact ⟨hBc ▸ h.ca, h_code⟩
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    have heq : benv = msg.benv := (Except.ok.inj h_run).symm
    subst heq
    exact h

/-! ## 4. Balance-sum relations and primitive state updates -/

def State.balSum (st : Jaune.State) : Nat :=
  sum st.bal

def Devm.balSum (d : Devm) : Nat :=
  State.balSum d.state

def State.BalNoninc (pre post : Jaune.State) : Prop :=
  State.balSum post ≤ State.balSum pre

def Devm.BalNoninc (pre post : Devm) : Prop :=
  Devm.balSum post ≤ Devm.balSum pre

def State.BalGrowth (allowance : Nat) (pre post : Jaune.State) : Prop :=
  State.balSum post ≤ State.balSum pre + allowance

def State.SumNof (st : Jaune.State) : Prop :=
  State.balSum st < 2 ^ 256

def Devm.SumNof (d : Devm) : Prop :=
  Devm.balSum d < 2 ^ 256

lemma balNoninc_refl_trans :
    (ReflexiveRel State.BalNoninc ∧ TransitiveRel State.BalNoninc) ∧
    (ReflexiveRel Devm.BalNoninc ∧ TransitiveRel Devm.BalNoninc) := by
  exact ⟨⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩,
         ⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩⟩

lemma Adr.toNat_lt_size (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr, Nat.lo]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma sumBelow_setBal_eq_local (st : Jaune.State) (a : Adr) (v : B256)
    (n : Nat) (hn : n ≤ a.toNat) (hsize : n ≤ 2 ^ 160) :
    sumBelow (fun x => (st.setBal a v).bal x) n =
      sumBelow (fun x => st.bal x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [ih (Nat.le_of_succ_le hn) (Nat.le_of_succ_le hsize)]
    have hnlt : n < a.toNat := Nat.lt_of_succ_le hn
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    have hne : n.toAdr ≠ a := by
      intro heq
      have hnat := congrArg Adr.toNat heq
      rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
      omega
    have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
      State.get_set_ne _ hne.symm _
    have hbal : (st.setBal a v).bal n.toAdr = st.bal n.toAdr := by
      dsimp [State.bal, State.setBal]
      have hget' : (st.set a ((st.get a).withBal v)).get n.toAdr =
          st.get n.toAdr := by
        simpa [State.setBal] using hget
      rw [hget']
    rw [hbal]

lemma sumBelow_setBal_add_local (st : Jaune.State) (a : Adr) (v : B256)
    (n : Nat) (hsize : n ≤ 2 ^ 160) (ha : a.toNat < n) :
    sumBelow (fun x => (st.setBal a v).bal x) n + (st.bal a).toNat =
      sumBelow (fun x => st.bal x) n + v.toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
    · have hih := ih (Nat.le_of_succ_le hsize) ha_lt
      have hne : n.toAdr ≠ a := by
        intro heq
        have hnat := congrArg Adr.toNat heq
        rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
        omega
      have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
        State.get_set_ne _ hne.symm _
      change sumBelow (fun x => (st.setBal a v).bal x) n +
          ((st.setBal a v).get n.toAdr).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get n.toAdr).bal.toNat + v.toNat
      rw [hget]
      omega
    · have hprefix := sumBelow_setBal_eq_local st a v n
        (Nat.le_of_eq ha_eq.symm) (Nat.le_of_succ_le hsize)
      have haddr : n.toAdr = a := by
        rw [← ha_eq]
        exact toAdr_toNat a
      rw [hprefix, haddr]
      change sumBelow (fun x => st.bal x) n +
          ((st.setBal a v).get a).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      dsimp [State.setBal]
      rw [State.get_set_self]
      change sumBelow (fun x => st.bal x) n + v.toNat +
          (st.get a).bal.toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      omega

lemma State.balSum_setBal (st : Jaune.State) (a : Adr) (v : B256) :
    State.balSum (st.setBal a v) + (st.bal a).toNat =
      State.balSum st + v.toNat := by
  have hmax : Adr.max.toNat.succ = 2 ^ 160 := by decide
  have ha : a.toNat < Adr.max.toNat.succ := by
    rw [hmax]
    exact Adr.toNat_lt_size a
  simpa [State.balSum, sum] using
    (sumBelow_setBal_add_local st a v Adr.max.toNat.succ
      (by rw [hmax]) ha)

lemma State.balSum_subBal {st mid : Jaune.State} {a : Adr} {v : B256}
    (h : st.subBal a v = some mid) :
    State.balSum mid + v.toNat = State.balSum st := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h_mid
    subst h_mid
    have h_set := State.balSum_setBal st a (st.bal a - v)
    rename_i h_not_lt
    have h_le : v ≤ st.bal a := le_of_not_gt h_not_lt
    have h_le2 : v.toNat ≤ (st.bal a).toNat := B256.toNat_le_toNat h_le
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_set
    omega

lemma State.addBal_growth (st : Jaune.State) (a : Adr) (v : B256) :
    State.BalGrowth v.toNat st (st.addBal a v) := by
  unfold State.addBal State.BalGrowth
  have h := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add] at h
  unfold Nat.lo at h
  have h_mod := Nat.mod_le ((st.bal a).toNat + v.toNat) (2^256)
  omega

/- This lemma is the reusable conservation/nonincrease theorem for value transfer,
   including the recipient-overflow case.  -/
lemma State.sub_addBal_noninc {st mid : Jaune.State}
    {src dst : Adr} {v : B256}
    (hsub : st.subBal src v = some mid) :
    State.BalNoninc st (mid.addBal dst v) := by
  dsimp [State.BalNoninc]
  have h1 := State.addBal_growth mid dst v
  dsimp [State.BalGrowth] at h1
  have h2 := State.balSum_subBal hsub
  omega

lemma State.setBal_zero_noninc (st : Jaune.State) (a : Adr) :
    State.BalNoninc st (st.setBal a 0) := by
  unfold State.BalNoninc
  have h := State.balSum_setBal st a 0
  have hz : ((0 : B256).toNat) = 0 := by decide
  rw [hz, Nat.add_zero] at h
  omega

lemma Devm.balNoninc_of_state {pre post : Devm}
    (h : State.BalNoninc pre.state post.state) : Devm.BalNoninc pre post := by
  exact h

lemma Devm.balNoninc_of_getBal_eq {pre post : Devm}
    (h : post.getBal = pre.getBal) : Devm.BalNoninc pre post := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum post.getBal ≤ sum pre.getBal
  rw [h]

/-! ## 5. Balance effects of instruction and message semantic units -/

def MessageExecution := Except (EvmError × Jaune.State × AdrSet × Tra) Devm

def MessageExecution.state : MessageExecution → Jaune.State
  | .ok d => d.state
  | .error ⟨_, st, _, _⟩ => st

def MessageExecution.Rel
    (R : Jaune.State → Jaune.State → Prop)
    (pre : Jaune.State) (out : MessageExecution) : Prop :=
  R pre out.state

/-- A successful message settlement either restored the message-entry world or
retained a clean successful message result unchanged at the world-state level. -/
theorem processMessage_settle_ok_state_cases
    {msg : Msg} {result : MessageExecution} {post : Devm}
    (h : processMessage.settle msg result = .ok post) :
    post.state = msg.benv.state ∨
      ∃ raw : Devm, result = .ok raw ∧
        raw.error.isSome = false ∧ post.state = raw.state := by
  cases result with
  | error error =>
      simp [processMessage.settle] at h
  | ok raw =>
      unfold processMessage.settle at h
      simp only [bind, Except.bind] at h
      cases herr : raw.error.isSome with
      | false =>
          rw [if_neg (by simpa using herr)] at h
          exact Or.inr ⟨raw, rfl, herr,
            (congrArg Devm.state (Except.ok.inj h)).symm⟩
      | true =>
          rw [if_pos herr] at h
          have heq := Except.ok.inj h
          exact Or.inl <| calc
            post.state =
                (raw.rollback msg.benv.state
                  msg.tenv.transientStorage).state :=
              (congrArg Devm.state heq).symm
            _ = msg.benv.state := rfl

/-- A no-slot core run is a failed entry or a precompile/empty-code execution.
On a successful wrapper result it either rolled back or retained exactly the
successful message-entry transfer; precompiles cannot alter the world. -/
theorem ProcessMessage.none_ok_state_cases
    {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post)) :
    post.state = msg.benv.state ∨
      ∃ benv, msg.benvAfterTransfer = .ok benv ∧
        post.state = benv.state := by
  rcases RunFrame.decompose hprocess with
    ⟨error, _htransfer, _hslot, hresult⟩ |
    ⟨benv, _result, htransfer, hexecute, hresult⟩
  · simp [Frame.ofCall, Frame.settleMsg,
      processMessage.settle] at hresult
  · change msg.benvAfterTransfer = .ok benv at htransfer
    change ExecuteCode (msg.withBenv benv) .none _result at hexecute
    change (.ok post) = processMessage.settle msg _result at hresult
    unfold ExecuteCode at hexecute
    cases hentry : executeCode.enter (msg.withBenv benv) with
    | inl evm =>
        rw [hentry] at hexecute
        rcases hexecute with ⟨raw, hslot, _⟩
        cases hslot
    | inr raw =>
        rw [hentry] at hexecute
        rcases executeCode.enter_inr hentry with ⟨address, hraw⟩
        rcases processMessage_settle_ok_state_cases hresult.symm with
          hrollback | ⟨clean, hclean, _hcleanError, hpost⟩
        · exact Or.inl hrollback
        · have hhandled :
              executeCode.handleError
                (executePrecomp (initEvm (msg.withBenv benv)) address) =
                  .ok clean := by
            rw [← hraw, ← hexecute.2, hclean]
          have hcleanState :=
            executeCode.handle_precompile_ok_state hhandled
          exact Or.inr ⟨benv, htransfer, hpost.trans hcleanState⟩

def BenvExecution.state : Except (EvmError × Jaune.State × AdrSet × Tra) Benv →
    Jaune.State
  | .ok benv => benv.state
  | .error ⟨_, st, _, _⟩ => st

/-! Error-side `getBal` frame lemmas, mirroring the generated `*_getCode_err`
family in `Blanc/Common.lean`: every regular-instruction error path leaves
balances unchanged. -/

lemma Rinst.inv_getBal_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getBal_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => s.bal) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getBal a).symm

lemma Rinst.balance_effect (r : Rinst) :
    Rinst.Effect Devm.BalNoninc r := by
  intro pc sevm pre out hrun
  cases out with
  | ok post => exact Devm.balNoninc_of_getBal_eq (Rinst.preserves_bal hrun).symm
  | error err => exact Devm.balNoninc_of_getBal_eq (funext fun a => Rinst.inv_getBal_err hrun a)

lemma Jinst.balance_effect (j : Jinst) :
    Jinst.Effect Devm.BalNoninc j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact Devm.balNoninc_of_getBal_eq
    (funext fun a => (hf.getBal a).symm)

lemma Ninst.push_balance_effectRec {xs : Bytes} {hxs : xs.length ≤ 32} :
    Ninst.EffectRec Devm.BalNoninc (.push xs hxs) := by
  exact Ninst.push_effectRec_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

lemma Linst.dest_balance_effect :
    Linst.Effect Devm.BalNoninc .dest := by
  intro sevm pre out run
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : pre.popToAdr <;> dsimp
  case error err =>
    intro run
    rw [← run]
    apply Devm.balNoninc_of_getBal_eq
    rw [Devm.popToAdr_err_snd h1]
  case ok res1 =>
    have hpop : res1.2.getBal = pre.getBal := by
      funext a
      exact Devm.popToAdr_getBal_eq h1 a
    have hacc :
        (if res1.1 ∉ res1.2.accessedAddresses then
            (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess)
          else (res1.2, gasSelfDestruct)).1.getBal = res1.2.getBal := by
      funext a
      split <;> rfl
    cases h2 : chargeGas
        (if ((if res1.1 ∉ res1.2.accessedAddresses then
                    (addAccessedAddress res1.2 res1.1,
                      gasSelfDestruct + gasColdAccountAccess)
                  else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧
              ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then
          (if res1.1 ∉ res1.2.accessedAddresses then
                (addAccessedAddress res1.2 res1.1,
                  gasSelfDestruct + gasColdAccountAccess)
              else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount
        else
          (if res1.1 ∉ res1.2.accessedAddresses then
              (addAccessedAddress res1.2 res1.1,
                gasSelfDestruct + gasColdAccountAccess)
            else (res1.2, gasSelfDestruct)).2)
        (if res1.1 ∉ res1.2.accessedAddresses then
            (addAccessedAddress res1.2 res1.1,
              gasSelfDestruct + gasColdAccountAccess)
          else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [chargeGas_err_snd h2]
      exact hacc.trans hpop
    case ok res2 =>
      have hpre : res2.getBal = pre.getBal := by
        funext a
        exact (chargeGas_getBal_eq h2 a).trans
          (congrFun (hacc.trans hpop) a)
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        have herr : err.2 = res2 := by
          dsimp [assertDynamic] at h3
          exact Except.assert_err_snd h3
        rw [herr]
        exact hpre
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget
            (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run
          rw [← run]
          exact Devm.balNoninc_of_getBal_eq hpre
        case some res3 =>
          have hsub : res2.state.subBal sevm.currentTarget
              (res1.2.getAcct sevm.currentTarget).bal = some res3.state := by
            dsimp [Devm.subBal, Option.bind] at h4
            cases hs : res2.state.subBal sevm.currentTarget
                (res1.2.getAcct sevm.currentTarget).bal
            · rw [hs] at h4
              contradiction
            · rw [hs] at h4
              injection h4 with heq
              subst heq
              rfl
          have htransfer : State.BalNoninc pre.state
              (res3.addBal res1.1
                (res1.2.getAcct sevm.currentTarget).bal).state := by
            have ht := State.sub_addBal_noninc (dst := res1.1) hsub
            have hbal : res2.state.bal = pre.state.bal := hpre
            unfold State.BalNoninc State.balSum at ht ⊢
            rw [hbal] at ht
            exact ht
          by_cases hdel : sevm.currentTarget ∈
              (res3.addBal res1.1
                (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [hdel, if_pos]
            intro run
            rw [← run]
            unfold Execution.Rel Outcome.Rel
            apply Devm.balNoninc_of_state
            apply balNoninc_refl_trans.1.2 htransfer
            exact State.setBal_zero_noninc _ _
          · simp only [hdel]
            intro run
            rw [← run]
            unfold Execution.Rel Outcome.Rel
            exact Devm.balNoninc_of_state htransfer

lemma Linst.balance_effect (l : Linst) :
    Linst.Effect Devm.BalNoninc l := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · exact Linst.dest_balance_effect
  · intro sevm pre out run
    have hf := Linst.run_instructionFrame sevm pre l h_not_dest
    rw [run] at hf
    cases out <;> exact Devm.balNoninc_of_getBal_eq
      (funext fun a => (hf.getBal a).symm)

/-- An instruction frame is balance-silent, hence transports directly to the
total-balance preorder used by the balance-effect layer. -/
lemma Devm.instructionFrame_refines_balNoninc :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.BalNoninc d d' := by
  intro pre post h
  apply Devm.balNoninc_of_state
  rw [h.state]
  exact balNoninc_refl_trans.1.1 _

lemma Msg.benvAfterTransfer_balance_effect {msg : Msg}
    {out : Except (EvmError × Jaune.State × AdrSet × Tra) Benv}
    (h : msg.benvAfterTransfer = out) :
    State.BalNoninc msg.benv.state (BenvExecution.state out) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h
    rw [h_stv] at h
    simp only [if_true] at h
    unfold Benv.subBal at h
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      exact Nat.le_refl _
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      change State.BalNoninc msg.benv.state (st_mid.addBal msg.currentTarget msg.value)
      exact State.sub_addBal_noninc h_sub
  · unfold Msg.benvAfterTransfer at h
    rw [if_neg h_stv] at h
    rw [← h]
    exact Nat.le_refl _

lemma processCreateMessage.chargeCodeGas_balance_effect
    {rules : ForkRules} {pre : Devm} {out : Execution}
    (h : processCreateMessage.chargeCodeGas rules pre = out) :
    Execution.Rel Devm.BalNoninc pre out := by
  rcases out with ⟨err, d⟩ | d <;> simp only [Execution.Rel, Outcome.Rel]
  · simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · simp only [Except.error.injEq] at h
      cases h
      exact balNoninc_refl_trans.2.1 pre
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · rename_i code neq ex errCharge hCharge
        simp only [Except.error.injEq] at h
        cases h
        have hstate := chargeGas_err_snd hCharge
        change d = pre at hstate
        rw [hstate]
        exact balNoninc_refl_trans.2.1 pre
      · split at h
        · simp only [Except.error.injEq] at h
          cases h
          rename_i code neq ex hSize hCharge
          have hb := Devm.burn_of_chargeGas hCharge
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state
        · cases h
  · simp only [id]
    simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · cases h
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i code neq ex hSize hCharge
          simp only [Except.ok.injEq] at h
          cases h
          have hb := Devm.burn_of_chargeGas hSize
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state

lemma executePrecomp_balance_effect {evm : Evm} {a : Adr} {out : Execution}
    (h : executePrecomp evm a = out) :
    Execution.Rel Devm.BalNoninc evm.dyna out := by
  subst out
  unfold executePrecomp applyPrecompResult Execution.Rel Outcome.Rel
    Devm.BalNoninc Devm.balSum State.balSum
  cases precompileRun evm a <;> rfl

/-- `executeCode.handleError` selects between the raw execution result and a
rolled-back state without introducing any balance write of its own, so it
transports a raw `Devm.BalNoninc` frame to a `State.BalNoninc` on the handled
message outcome. -/
lemma executeCode.handleError_balance_effect {pre : Devm} {raw : Execution}
    {handled : MessageExecution}
    (hb : Execution.Rel Devm.BalNoninc pre raw)
    (hh : executeCode.handleError raw = handled) :
    State.BalNoninc pre.state (MessageExecution.state handled) := by
  rcases raw with ⟨err, d⟩ | d
  · cases err <;>
      (simp only [executeCode.handleError] at hh; subst handled; exact hb)
  · simp only [executeCode.handleError] at hh
    subst handled
    exact hb

/-- Frame projections of the two child messages, as explicit equations: the
defeq is cheap to state and expensive to re-derive at every use site. -/
lemma callMsg_benv_state
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {calldata : Bytes}
    {code : ByteArray} {dp : Bool} :
    ( callMsg sevm evm1 gas value caller target codeAddress stv isSt calldata
        code dp ).benv.state = evm1.state := rfl

lemma createMsg_benv_state
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.state
      = devm.state := rfl

/-- The create driver is the call driver on the seeded message, followed by the
create-specific settlement. -/
lemma processCreateMessage_eq (msg : Msg) :
    processCreateMessage msg =
      processCreateMessage.settle msg
        (processMessage (processCreateMessage.msg msg)) := by
  unfold processCreateMessage processMessage runFrame Frame.enter Frame.settle
    Frame.settleMsg Frame.ofCreate Frame.ofCall
  rcases (processCreateMessage.msg msg).benvAfterTransfer with e | benv <;>
    simp only [reduceIte]
  · rfl
  · rcases executeCode.enter ((processCreateMessage.msg msg).withBenv benv) with
      evm | raw
    · rfl
    · rfl

lemma processCreateMessage.settle_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × Tra} :
    processCreateMessage.settle msg (.error e) = .error e := rfl

/-- A failed child message aborts the CREATE-family return path. -/
lemma Resume.create_run_error {parent : Devm} {newAddress : Adr}
    {e : EvmError × Jaune.State × AdrSet × Tra} {sf : Devm}
    (h : (Resume.create parent newAddress).run (.error e) = .ok sf) : False := by
  rcases e with ⟨err, st, ac, tra⟩
  unfold Resume.run liftToExecution at h
  cases h

lemma processMessage.settle_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × Tra} :
    processMessage.settle msg (.error e) = .error e := rfl

/-- **Message settlement inverted.**  A frame that settles `.ok` came from an
`.ok` sub-result, and the settled state is either that sub-result rolled back
to the message's entry world, or the sub-result itself — according to whether
it carried an error.

This is the general shape that `processMessage.settle_ok_gasLe` upstream
projects onto gas.  Consumers previously re-derived it inline: dispatch the
`.error` arm through `settle_error`, unfold the settle, and split on
`evm.error.isSome`.  Taking the disjunction directly replaces that walk with a
single `rcases`, and keeps the rollback's world arguments named rather than
re-elaborated at each site. -/
theorem processMessage.settle_ok_cases {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × Tra) Devm} {post : Devm}
    (hset : processMessage.settle msg r = .ok post) :
    ∃ evm : Devm, r = .ok evm ∧
      (evm.error.isSome = true ∧
          evm.rollback msg.benv.state msg.tenv.transientStorage = post
        ∨ ¬ evm.error.isSome = true ∧ evm = post) := by
  cases r with
  | error e => exact absurd hset (by rw [processMessage.settle_error]; simp)
  | ok evm =>
    refine ⟨evm, rfl, ?_⟩
    unfold processMessage.settle at hset
    dsimp only [bind, Except.bind] at hset
    by_cases herr : evm.error.isSome = true
    · rw [if_pos herr] at hset
      exact .inl ⟨herr, Except.ok.inj hset⟩
    · rw [if_neg herr] at hset
      exact .inr ⟨herr, Except.ok.inj hset⟩

/-- Master balance effect for the code-execution layer: running the callee's
code (interpreter, precompile, or the empty-code no-op) never increases the
total balance relative to the freshly-initialised message state. The `Xlot`
witness carries the interpreter's own `Devm.BalNoninc` frame; the precompile
branch supplies its frame directly. -/
lemma ExecuteCode.balance_effect {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (hec : ExecuteCode msg xl ex) :
    State.BalNoninc (initEvm msg).dyna.state (MessageExecution.state ex) := by
  unfold ExecuteCode at hec
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at hec
  · rcases hec with ⟨raw, hxl_eq, hh⟩
    rw [hxl_eq] at hxl
    rw [executeCode.enter_inl henter] at hxl
    exact executeCode.handleError_balance_effect hxl hh.symm
  · obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    refine executeCode.handleError_balance_effect ?_ hec.2.symm
    rw [hraw]
    exact executePrecomp_balance_effect rfl

lemma ProcessMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with ⟨err, st, ac, tra⟩ | benv <;>
    rw [h_benv] at hbody
  · rw [hbody.2, processMessage.settle_error]
    have ht := Msg.benvAfterTransfer_balance_effect h_benv
    simp only [MessageExecution.Rel, MessageExecution.state,
      BenvExecution.state] at ht ⊢
    exact ht
  · have htransfer := Msg.benvAfterTransfer_balance_effect h_benv
    have hexec : State.BalNoninc benv.state (MessageExecution.state r0) := by
      have h := ExecuteCode.balance_effect hxl hbody
      have hinit : (initEvm (msg.withBenv benv)).dyna.state = benv.state := rfl
      rwa [hinit] at h
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact Nat.le_trans hexec htransfer
    · dsimp only [bind, Except.bind]
      split
      · exact balNoninc_refl_trans.1.1 _
      · exact Nat.le_trans hexec htransfer

lemma ProcessCreateMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessCreateMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  obtain ⟨ex', run_pm, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_seed : (processCreateMessage.msg msg).benv.state.bal = msg.benv.state.bal := by
    change ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget).bal = msg.benv.state.bal
    rw [State.incrNonce_bal, State.setStor_bal]
  have h_pm := ProcessMessage.balance_effect hxl run_pm
  unfold MessageExecution.Rel State.BalNoninc State.balSum at h_pm
  rw [h_seed] at h_pm
  unfold processCreateMessage.settle
  rcases ex' with e' | evm
  · exact h_pm
  · dsimp only [bind, Except.bind]
    split
    · cases h_cg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum
          State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        cases err_msg
        case halt => exact balNoninc_refl_trans.1.1 _
        all_goals exact Nat.le_trans h_charge h_pm
      | ok devm_charge =>
        dsimp only []
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum
          State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        change sum (devm_charge.state.setCode msg.currentTarget
          ⟨⟨devm_charge.output⟩⟩).bal ≤ sum msg.benv.state.bal
        rw [State.setCode_bal]
        exact Nat.le_trans h_charge h_pm
    · exact balNoninc_refl_trans.1.1 _

/-- The create prefix's sender nonce bump is a non-balance world write. -/
lemma Devm.incrNonce_balance_effect (pre : Devm) (a : Adr) :
    Devm.BalNoninc pre (pre.incrNonce a) := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum (pre.state.incrNonce a).bal ≤ sum pre.state.bal
  rw [State.incrNonce_bal]

/-- Child-error incorporation installs the child's already-accounted world;
the parent fields it retains do not include balances. -/
lemma incorporateChildOnError_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildOnError parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildOnError]
  exact h

/-- Child-success incorporation has the same precise balance projection as
the error form, while differing in the non-balance fields it incorporates. -/
lemma incorporateChildOnSuccess_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildOnSuccess parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildOnSuccess]
  exact h

/-- Pushing a status word and writing the returned output to memory are both
frame moves, so they carry a balance bound on the incorporated machine. -/
lemma Devm.pushMemWrite_balance {pre d : Devm} {v : B256} {oi : Nat} {o : Bytes}
    (h : Devm.BalNoninc pre d) :
    Execution.Rel Devm.BalNoninc pre
      (d.push v >>= fun d' => .ok (d'.memWrite oi o)) := by
  refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 h ?_
  refine Execution.Rel.bind balNoninc_refl_trans.2.2
    (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
      (Devm.push_instructionFrame v d)) ?_
  intro d'
  exact Devm.instructionFrame_refines_balNoninc
    (Devm.memWrite_instructionFrame d' oi o)

/-- A status push onto a machine already bounded against `pre` keeps the
bound, on both outcomes. -/
lemma Devm.push_balance_gen {v : B256} {pre d : Devm} {ex : Execution}
    (h : Devm.push v d = ex) (hf : Devm.BalNoninc pre d) :
    Execution.Rel Devm.BalNoninc pre ex := by
  subst h
  exact Execution.Rel.trans_left balNoninc_refl_trans.2.2 hf
    (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
      (Devm.push_instructionFrame v d))

/-- The CREATE-family return path never raises the parent's balance sum: the
child's world is already bounded and the status push is a frame move. -/
lemma Resume.create_balance {parent : Devm} {newAddress : Adr}
    {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent
      ((Resume.create parent newAddress).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;> dsimp only [bind, Except.bind]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
        (incorporateChildOnError_balance_effect h)
        (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
          (Devm.push_instructionFrame 0 _))
    · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
        (incorporateChildOnSuccess_balance_effect h)
        (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
          (Devm.push_instructionFrame _ _))

/-- The CALL-family return path, likewise: incorporation plus a push and a
memory write. -/
lemma Resume.call_balance {parent : Devm} {oi os : Nat} {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent ((Resume.call parent oi os).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;> dsimp only [bind, Except.bind]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · exact Devm.pushMemWrite_balance (incorporateChildOnError_balance_effect h)
    · exact Devm.pushMemWrite_balance (incorporateChildOnSuccess_balance_effect h)

/-- Canonical balance-effect master for generic calls.  The call prefix is
balance-silent; all balance changes are delegated to `ProcessMessage`, and
child incorporation merely installs the child's already-bounded state. -/
lemma GenericCall.balanceEffect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hret : Devm.BalNoninc pre (pre.withReturnData []) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hret ?_
    refine Resume.call_balance ?_
    have h := ProcessMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rwa [callMsg_benv_state] at h

lemma GenericCall.balance_effect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out :=
  GenericCall.balanceEffect hxl run

/-- Canonical balance-effect master for generic creates.  Unlike calls, its
prefix contains the sender nonce write and its child path performs fresh
account initialisation before installing the child world. -/
lemma GenericCreate.balanceEffect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hgas : Devm.BalNoninc pre
      (pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  have hret : Devm.BalNoninc pre
      ((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData []) :=
    balNoninc_refl_trans.2.2 hgas
      (Devm.instructionFrame_refines_balNoninc
        (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))
  have hnonce : Devm.BalNoninc pre
      (addAccessedAddress
        (((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress) := by
    refine balNoninc_refl_trans.2.2 hret ?_
    refine balNoninc_refl_trans.2.2
      (Devm.incrNonce_balance_effect _ sevm.currentTarget) ?_
    exact Devm.instructionFrame_refines_balNoninc
      (addAccessedAddress_instructionFrame _ newAddress)
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact balNoninc_refl_trans.2.1 _
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact hgas
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Devm.push_balance_gen heq hnonce
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Devm.push_balance_gen heq hnonce
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hnonce ?_
    refine Resume.create_balance ?_
    have h := ProcessCreateMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rwa [createMsg_benv_state] at h

lemma GenericCreate.balance_effect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out :=
  GenericCreate.balanceEffect hxl run

lemma Xinst.balance_effectRec (x : Xinst) :
    Xinst.EffectRec Devm.BalNoninc x := by
  intro sevm pre xl out hxl run
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm pre x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at run
  -- the whole step stayed inside the instruction frame
  · obtain ⟨-, rfl⟩ := run
    exact Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc hframe
  -- dispatched to the CREATE family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCreate.balanceEffect hxl run)
  -- dispatched to the CALL family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCall.balanceEffect hxl run)

lemma Ninst.balance_effectRec (n : Ninst) :
    Ninst.EffectRec Devm.BalNoninc n := by
  cases n
  case reg r =>
    apply Ninst.effectRec_reg
    apply Rinst.balance_effect
  case exec x =>
    apply Ninst.effectRec_exec
    apply Xinst.balance_effectRec
  case push xs hxs =>
    apply Ninst.push_balance_effectRec

theorem Exec.balance_effect {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    Execution.Rel Devm.BalNoninc pre out :=
  Exec.effect balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2 Ninst.balance_effectRec Jinst.balance_effect Linst.balance_effect run

lemma Ninst.balance_effect (n : Ninst) : Ninst.Effect Devm.BalNoninc n := by
  apply Ninst.effect_of_effectRec balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
  · exact Ninst.balance_effectRec
  · exact Jinst.balance_effect
  · exact Linst.balance_effect

theorem Func.balance_effect {fs : List Func} {sevm : Sevm}
    {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : Devm.BalNoninc pre post := by
  apply Func.effect (R := Devm.BalNoninc) (htrans := balNoninc_refl_trans.2.2) _ _ Ninst.balance_effect Linst.balance_effect run
  · intro xs pr po hpop
    apply Devm.balNoninc_of_state
    rw [hpop.state]
    exact balNoninc_refl_trans.1.1 _
  · intro pr po hburn
    apply Devm.balNoninc_of_state
    rw [hburn.state]
    exact balNoninc_refl_trans.1.1 _

/-! ## 6. Executable wrappers and the Solvent.lean endpoint -/

lemma Xlot.balance_rel_of_filled {xl : Xlot}
    (hfill : xl.Filled) :
    Xlot.Rel Devm.BalNoninc xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · constructor
  · rcases hfill with ⟨exc⟩
    exact Exec.balance_effect exc

lemma processMessage_balance_noninc {msg : Msg} {post : Devm}
    (h : processMessage msg = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  obtain ⟨xl, hfill, hrun⟩ := of_processMessage msg (.ok post) h
  have heff := ProcessMessage.balance_effect (Xlot.balance_rel_of_filled hfill) hrun
  change State.BalNoninc msg.benv.state post.state at heff
  exact heff

lemma processCreateMessage_balance_noninc
    {msg : Msg} {post : Devm}
    (h : processCreateMessage msg = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  rcases of_processCreateMessage msg (.ok post) h with ⟨xl, hfill, hrun⟩
  have hxl : Xlot.Rel Devm.BalNoninc xl := Xlot.balance_rel_of_filled hfill
  have heff := ProcessCreateMessage.balance_effect hxl hrun
  exact heff

lemma setDelegationStep_bal_eq {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; rfl
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            show ((msg.benv.state.setCode _ _).incrNonce _).bal =
              msg.benv.state.bal
            rw [State.incrNonce_bal, State.setCode_bal]

lemma setDelegationLoop_bal_eq {auths : List Auth} {msg msg' : Msg}
    {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  induction auths generalizing msg rc with
  | nil =>
    unfold setDelegationLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons auth auths ih =>
    unfold setDelegationLoop at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p h_step
      obtain ⟨msgS, rcS⟩ := p
      exact (ih h).trans (setDelegationStep_bal_eq h_step)

lemma setDelegation_balSum_eq {msg msg' : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨msg', refund⟩) :
    State.balSum msg'.benv.state = State.balSum msg.benv.state := by
  unfold setDelegation at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p h_loop
    obtain ⟨msgL, rcL⟩ := p
    have h_bal := setDelegationLoop_bal_eq h_loop
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      unfold State.balSum
      rw [show ({ msgL with
        code := msgL.benv.state.getCode _ } : Msg).benv.state.bal =
          msgL.benv.state.bal from rfl, h_bal]

lemma processMessageCall.call_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall.call msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.call at h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processMessage_balance_noninc h_pm
        have hpre : State.BalNoninc msg.benv.state evm'.state := by
          split at hbal <;> exact hbal
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hpre
  · rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgD, val⟩⟩
    · simp only [h_del, bind, Except.bind] at h
      injection h
    · simp only [h_del, bind, Except.bind] at h
      have h_sum := setDelegation_balSum_eq h_del
      unfold Except.bimap at h
      split at h
      · injection h
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have hbal := processMessage_balance_noninc h_pm
          have hpre : State.BalNoninc msg.benv.state evm'.state := by
            have hD : State.BalNoninc msgD.benv.state evm'.state := by
              split at hbal <;> exact hbal
            unfold State.BalNoninc at *
            omega
          split at h
          · split at h
            · injection h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩
              exact hpre
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre

lemma processMessageCall.create_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall.create msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.create at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    exact le_refl _
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processCreateMessage_balance_noninc h_pm
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hbal
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hbal

lemma processMessageCall_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall at h
  split at h
  · exact processMessageCall.create_balance_noninc h
  · exact processMessageCall.call_balance_noninc h

lemma processMessageCall_sum_le
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    sum post.bal ≤ sum msg.benv.state.bal := by
  exact processMessageCall_balance_noninc h


/-! ## The shared ERC-20 proof layer

The lemma half of the hoist whose definition half is `Blanc/CommonCore.lean`'s
*The shared ERC-20 surface*. Every declaration below arrived here from
`Blanc/Solvent.lean` byte-identically in statement and proof: each one mentions
no contract-specific constant once the shared definitions moved up, so none was
ever WETH's, and `Blanc/Conserved.lean` -- which may not import a sibling
contract's module -- needs them as much as `Blanc/Solvent.lean` does.

Placement within the shared layer follows what each declaration mentions.
Anything stated in terms of `Increase`/`Decrease`/`Transfer` had to land in
`Blanc/Ladder.lean` instead, since that algebra is defined below this module:
`incrAt_of_incrWbal`, `of_transferFromUpdateSbal` and `transfer_of_transfer`
are there, immediately after `transfer_preserves_sum`. -/

/-! ### Address-shaped words -/

theorem validAdr_toB256 (a : Adr) : ValidAdr a.toB256 := ⟨a, rfl⟩

lemma toB256_toAdr {w : B256} :
    ValidAdr w → w.toAdr.toB256 = w := by
  intro h; rcases h with ⟨a, ha⟩;
  rw [← ha, toAdr_toB256]

lemma pref_cons {α} {x : α} {xs ys : List α}
    (h : xs <<+ ys) : (x :: xs) <<+ (x :: ys) := by
  rcases h with ⟨t, h⟩
  refine ⟨t, ?_⟩
  simp only [Split] at h ⊢
  rw [h]
  rfl

lemma cons_pref_cons_inv {α} {x : α} {xs ys : List α} (h : (x :: xs) <<+ (x :: ys)) : xs <<+ ys := by
  rcases h with ⟨zs, h⟩
  injection h with _ h_tail
  exact ⟨zs, h_tail⟩

/-! ### Line-walking tactics

`line_execute` and `line_execute_with` split a `Line.Run` goal at a chosen
instruction count and name the intermediate state. They lived in
`Blanc/Solvent.lean`, which put them out of reach of any second contract; their
whole supporting cast (`run_append_elim`, `findSubscript`, `Strings.intro`)
is in `Blanc/Tactics.lean`, upstream of here. -/

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq

def Line.take : Nat → Q(Line) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, l => do
  let l' : Q(Line) ← Lean.Meta.whnf l
  match l' with
  | ~q([]) => failure
  | ~q($i :: $is) =>
    let x ← Line.take n is
    pure q($i :: $x)
  | _ => failure

elab "line_execute" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s $l _ → $c) =>
      let ss ← findSubscript s
      let x ← Line.take n l
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for line_execute"

elab "line_execute_with" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for line_execute_with"

end

/-! ### The address mask, and what the two address guards yield -/

lemma B128.and_eq_and_prod_and (x y : B128) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B256.and_eq_and_prod_and (x y : B256) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

/-! A bitwise `or` is zero only if both its operands are.

The fact every *composite* guard needs: a guard built as `or` of two clauses
passes exactly when both clauses pass, so the one flag the walk sees on the
stack yields both conjuncts.  `Blanc/Fmint.lean`'s `checkSlotCollides` is the
first such guard; `checkAddress`, being a single clause, never needed this. -/

theorem UInt64.of_or_eq_zero {x y : UInt64} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have hb := congrArg UInt64.toBitVec h
  rw [UInt64.toBitVec_or, UInt64.toBitVec_zero, BitVec.or_eq_zero_iff] at hb
  exact ⟨UInt64.toBitVec_inj.mp (by rw [hb.1]; rfl),
         UInt64.toBitVec_inj.mp (by rw [hb.2]; rfl)⟩

theorem B128.of_or_eq_zero {x y : B128} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have h1 : x.1 ||| y.1 = 0 := congrArg (fun z : B128 => z.1) h
  have h2 : x.2 ||| y.2 = 0 := congrArg (fun z : B128 => z.2) h
  exact ⟨Prod.ext (UInt64.of_or_eq_zero h1).1 (UInt64.of_or_eq_zero h2).1,
         Prod.ext (UInt64.of_or_eq_zero h1).2 (UInt64.of_or_eq_zero h2).2⟩

theorem B256.of_or_eq_zero {x y : B256} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have h1 : x.1 ||| y.1 = 0 := congrArg (fun z : B256 => z.1) h
  have h2 : x.2 ||| y.2 = 0 := congrArg (fun z : B256 => z.2) h
  exact ⟨Prod.ext (B128.of_or_eq_zero h1).1 (B128.of_or_eq_zero h2).1,
         Prod.ext (B128.of_or_eq_zero h1).2 (B128.of_or_eq_zero h2).2⟩

/-! A word and its complement sum to the all-ones value, with no carry at any
bit — so a bound of the form `y ≤ ~~~ x` is exactly a no-overflow guarantee
for `x + y`.  The fact a *complement-shaped* bound check needs: fmint's
`maxFlashLoan = not supply` is the first user, and the reason its
`amount ≤ maxFlashLoan` guard is the entire overflow argument for the mint. -/

lemma UInt64.toNat_add_not (x : UInt64) : x.toNat + (~~~x).toNat = 2 ^ 64 - 1 := by
  rw [UInt64.toNat_not]
  have h := UInt64.toNat_lt x
  simp only [UInt64.size] at *
  omega

/-- `B128.toNat`'s shift-or decomposition, as plain arithmetic: the low word
sits strictly below the shifted high word, so the `|||` is an `+`. -/
lemma B128.toNat_eq (x : B128) : x.toNat = x.1.toNat * 2 ^ 64 + x.2.toNat := by
  simp only [B128.toNat]
  rw [← Nat.add_eq_or (by rw [Nat.shiftLeft_eq]; exact Nat.dvd_mul_left _ _) (UInt64.toNat_lt _),
    Nat.shiftLeft_eq]

lemma B256.toNat_eq (x : B256) : x.toNat = x.1.toNat * 2 ^ 128 + x.2.toNat := by
  simp only [B256.toNat]
  rw [← Nat.add_eq_or (by rw [Nat.shiftLeft_eq]; exact Nat.dvd_mul_left _ _) B128.toNat_lt,
    Nat.shiftLeft_eq]

lemma B128.toNat_add_not (x : B128) : x.toNat + (~~~x).toNat = 2 ^ 128 - 1 := by
  have h1 := UInt64.toNat_add_not x.1
  have h2 := UInt64.toNat_add_not x.2
  have hc : (~~~x) = ⟨~~~x.1, ~~~x.2⟩ := rfl
  rw [B128.toNat_eq, B128.toNat_eq, hc]
  simp only []
  omega

lemma B256.toNat_add_not (x : B256) : x.toNat + (~~~x).toNat = 2 ^ 256 - 1 := by
  have h1 := B128.toNat_add_not x.1
  have h2 := B128.toNat_add_not x.2
  have hc : (~~~x) = ⟨~~~x.1, ~~~x.2⟩ := rfl
  rw [B256.toNat_eq, B256.toNat_eq, hc]
  simp only []
  omega

/-- A word whose complement is zero is the all-ones word — and the converse.

The fact a `[not, iszero]` pair yields: fmint's `isMax`, the infinite-allowance
test, is exactly that pair, so a walk that has read the flag learns whether the
allowance it loaded is `type(uint256).max`.  Proved from `toNat_add_not` rather
than by cases on the four `UInt64` limbs. -/
lemma B256.eq_max_of_not_eq_zero {x : B256} (h : ~~~ x = 0) : x = B256.max := by
  have h1 := B256.toNat_add_not x
  rw [h, show (0 : B256).toNat = 0 from rfl] at h1
  have h2 : x.toNat = B256.max.toNat := by
    rw [show B256.max.toNat = 2 ^ 256 - 1 from rfl]
    omega
  rw [← toB256_toNat x, h2, toB256_toNat]

lemma B256.not_max : (~~~ (B256.max : B256)) = 0 := rfl

/-- Every word is at most `B256.max`.  Small, but it is what makes "the
allowance is below the amount" already say "the allowance is not the infinite
one": the two arms of an `isMax` allowance test cannot both be escaped. -/
lemma B256.le_max (x : B256) : x ≤ B256.max := by
  rcases B256.le_or_gt x B256.max with h | h
  · exact h
  · exfalso
    have h1 := B256.toNat_lt_toNat h
    have h2 := B256.toNat_lt x
    rw [show (B256.max : B256).toNat = 2 ^ 256 - 1 from rfl] at h1
    omega

/-- The whole overflow argument for a complement-bounded add: `y ≤ ~~~ x` says
exactly that `x + y` does not overflow. -/
lemma B256.nof_of_le_not {x y : B256} (h : y ≤ ~~~ x) : B256.Nof x y := by
  have h1 := B256.toNat_add_not x
  have h2 := B256.toNat_le_toNat h
  unfold B256.Nof
  omega

/-- The converse of `B256.nof_of_le_not`: a non-overflowing add is exactly one
whose second operand is within the complement of the first.  Together the two
say that "`x + y` does not overflow" and "`y ≤ 2 ^ 256 - 1 - x`" are the same
statement — which is what lets a contract's `amount ≤ maxFlashLoan` guard be
read off a `B256.Nof` fact and vice versa. -/
lemma B256.le_not_of_nof {x y : B256} (h : B256.Nof x y) : y ≤ ~~~ x := by
  rcases B256.le_or_gt y (~~~ x) with h' | h'
  · exact h'
  · exfalso
    have h1 := B256.toNat_lt_toNat h'
    have h2 := B256.toNat_add_not x
    unfold B256.Nof at h
    omega

lemma B128.zero_and {x : B128} : 0 &&& x = 0 := by
  simp [B128.and_eq_and_prod_and]
  apply Prod.ext <;> change (0 : UInt64) &&& _ = 0 <;> apply UInt64.zero_and

lemma UInt64.mask_and_eq_zero (x : UInt32) :
    (0xffffffff00000000 : UInt64) &&& x.toUInt64 = 0 := by
  rw [← @UInt32.and_neg_one x, UInt32.toUInt64_and]
  rw [UInt64.and_comm (UInt32.toUInt64 _), ← UInt64.and_assoc]
  apply UInt64.zero_and

lemma UInt64.toUInt32_toUInt64_eq_of_highMask_and_eq_zero {x : UInt64}
    (h : (0xffffffff00000000 : UInt64) &&& x = 0) :
    x.toUInt32.toUInt64 = x := by
  apply UInt64.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt64, UInt64.toBitVec_toUInt32]
  apply BitVec.eq_of_getElem_eq_iff.mpr
  intro i hi
  rw [BitVec.getElem_setWidth]
  by_cases hi32 : i < 32
  · rw [BitVec.getLsbD_eq_getElem hi32, BitVec.getElem_setWidth,
      BitVec.getLsbD_eq_getElem (by omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    have hb := congrArg UInt64.toBitVec h
    rw [UInt64.toBitVec_and, UInt64.toBitVec_zero] at hb
    have hb_i := congrArg (fun v : BitVec 64 => v[i]) hb
    simp only [BitVec.getElem_and hi, BitVec.getElem_zero hi] at hb_i
    have hmask : ((0xffffffff00000000 : UInt64).toBitVec)[i] = true := by
      change (((-1 : UInt64) <<< 32).toBitVec)[i] = true
      rw [UInt64.toBitVec_shiftLeft, BitVec.getElem_shiftLeft' hi]
      simp [hi32]
      change (BitVec.allOnes 64)[i - 32] = true
      rw [BitVec.getElem_eq_testBit_toNat _ _ (by omega), BitVec.toNat_allOnes]
      rw [Nat.testBit_two_pow_sub_succ (x := 0) (by norm_num)]
      have hi64 : i - 32 < 64 := by omega
      simp [hi64]
    rw [hmask] at hb_i
    exact hb_i.symm

lemma validAdr_iff {w : B256} :
    ValidAdr w ↔ addressMask &&& w = 0 := by
  constructor <;> intro h
  · rcases h with ⟨⟨a32, a128⟩, ⟨_⟩⟩
    simp [Adr.toB256, addressMask]
    rw [B256.and_eq_and_prod_and]
    simp [B128.zero_and]
    rw [B128.and_eq_and_prod_and]
    simp
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply UInt64.mask_and_eq_zero
    · rfl
  · refine' ⟨w.toAdr, _⟩
    rcases w with ⟨⟨wz, wh⟩, wl⟩
    simp only [addressMask, B256.and_eq_and_prod_and, B128.and_eq_and_prod_and] at h
    have hz := congrArg (fun x : B256 => x.1.1) h
    have hm := congrArg (fun x : B256 => x.1.2) h
    change UInt64.max &&& wz = 0 at hz
    change (0xffffffff00000000 : UInt64) &&& wh = 0 at hm
    have h_wz : wz = 0 := by
      simp only [UInt64.max] at hz
      change (-1 : UInt64) &&& wz = 0 at hz
      simpa using hz
    have h_wh : wh.toUInt32.toUInt64 = wh := by
      exact UInt64.toUInt32_toUInt64_eq_of_highMask_and_eq_zero hm
    simp only [B256.toAdr, Adr.toB256, h_wz, h_wh]

lemma addressMask_eq_shl :
    addressMask = (~~~ (0 : B256)) <<< (160 : Nat).toB256.toNat := by
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)]; rfl

lemma of_push_addressMask {e : Sevm} {s s' : Devm} {xs}
    (h_pfx : xs <<+ s.stack) (h_run : Line.Run e s pushAddressMask s') :
    (addressMask :: xs <<+ s'.stack) := by
  rw [addressMask_eq_shl]
  revert s; simp only [pushAddressMask]; line_prefix

lemma of_check_non_address {e : Sevm} {s s' : Devm} {x xs}
    (h_pfx : x :: xs <<+ s.stack) (h_run : Line.Run e s checkNonAddress s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr x) := by
  rename' s' => s''
  rcases of_run_append _ h_run with ⟨sm, h_push, h_and⟩; clear h_run
  have h_pfx' := of_push_addressMask h_pfx h_push; clear h_pfx h_push s
  have h_pfx2 : (addressMask &&& x) :: xs <<+ s''.stack := by
    revert h_and; revert sm; line_prefix
  refine ⟨_, h_pfx2, Iff.symm validAdr_iff⟩

/-- `arg k ++ checkNonAddress`, the composite an address-shaped argument guard
tests: the masked word is zero exactly when the argument's head word is
address-shaped.  Contract-neutral, so it lives here rather than in the first
family that needed it. -/
theorem prefix_of_argCheckNonAddress {e : Sevm} {s s' : Devm} {k : B256}
    {xs : Stack} (hp : xs <<+ s.stack)
    (run : Line.Run e s (arg k ++ checkNonAddress) s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr (Sevm.argWord e k)) := by
  rcases of_run_append (arg k) run with ⟨_mid, r1, r2⟩
  exact of_check_non_address (prefix_of_arg hp r1) r2

lemma of_check_address {e : Sevm} {s s' : Devm} {x xs} :
    (x :: xs <<+ s.stack) →
    Line.Run e s checkAddress s' →
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ¬ ValidAdr x) := by
  rename' s' => s''; intros h_pfx h_run
  rcases of_run_append _ h_run with ⟨sm, hs', h_run'⟩; clear h_run
  rcases of_check_non_address h_pfx hs' with ⟨y, h_pfx', h_iff⟩; clear h_pfx hs' s
  have h_pfx2 : ((y =? 0) :: xs <<+ s''.stack) := by
    revert h_run'; revert sm; line_prefix
  refine' ⟨_, h_pfx2, _⟩; rw [← h_iff]
  apply Ne.ite_eq_right_iff <| Ne.symm B256.zero_ne_one

/-! ### `sstore`'s effect on storage -/

/-- Replacing the machine component before an accessed-storage-key update is
irrelevant once the caller supplies the final machine component. -/
@[simp] theorem Devm.addAccessedStorageKey_setMach_setMach
    {base : Devm} {target : Adr} {key : B256} {mach mach' : Mach} :
    (addAccessedStorageKey (base.setMach mach) target key).setMach mach' =
      (addAccessedStorageKey base target key).setMach mach' := rfl

lemma setStorVal_getStor_self {devm : Devm} {adr : Adr} {key val : B256} :
    Devm.getStor (devm.setStorVal adr key val) adr = (Devm.getStor devm adr).set key val := by
  simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
    Devm.setWorld, State.setStorVal]
  simp only [Devm.state, State.get_set_self]

/-- Persistent storage read-after-write at the same address and key. -/
@[simp] theorem Devm.getStorVal_setStorVal_self
    (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setStorVal adr key val).getStorVal adr key = val := by
  show (Devm.getStor (devm.setStorVal adr key val) adr).get key = val
  rw [setStorVal_getStor_self, Stor.get_set_self]

/-- Persistent storage writes preserve every account's code. -/
lemma Devm.setStorVal_getCode (devm : Devm) (owner : Adr)
    (key value : B256) (address : Adr) :
    (devm.setStorVal owner key value).getCode address =
      devm.getCode address := by
  show ((devm.state.setStorVal owner key value).get address).code =
    (devm.state.get address).code
  unfold State.setStorVal
  by_cases h : owner = address
  · subst h
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

/-- Installing account code preserves the frame log sequence. -/
lemma Devm.setCode_logs (devm : Devm) (address : Adr)
    (code : ByteArray) :
    (devm.setCode address code).logs = devm.logs := by
  rfl

/-- Installing account code preserves every account's persistent storage. -/
lemma Devm.setCode_getStor (devm : Devm) (address : Adr)
    (code : ByteArray) :
    Devm.getStor (devm.setCode address code) = Devm.getStor devm := by
  funext target
  change ((devm.state.setCode address code).get target).stor =
    (devm.state.get target).stor
  unfold State.setCode
  by_cases h : address = target
  · subst h
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

/-- Installing account code preserves the frame output bytes. -/
lemma Devm.setCode_output (devm : Devm) (address : Adr)
    (code : ByteArray) :
    (devm.setCode address code).output = devm.output := by
  rfl

/-- Installing account code preserves the frame error marker. -/
lemma Devm.setCode_error (devm : Devm) (address : Adr)
    (code : ByteArray) :
    (devm.setCode address code).error = devm.error := by
  rfl

/-- Installing account code preserves the frame refund counter. -/
lemma Devm.setCode_refundCounter (devm : Devm) (address : Adr)
    (code : ByteArray) :
    (devm.setCode address code).refundCounter = devm.refundCounter := by
  rfl

/-- Installing account code preserves the deletion-set accumulator. -/
lemma Devm.setCode_accountsToDelete (devm : Devm) (address : Adr)
    (code : ByteArray) :
    (devm.setCode address code).accountsToDelete = devm.accountsToDelete := by
  rfl

/-! ### Reusable projection cuts for compiled RETURN and SSTORE posts -/

/-- A `setMach`/`memRead`/`withOutput` return post preserves the base world. -/
lemma Devm.retPost_world (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) :
    ((((devm.setMach ⟨stack, devm.memory, gas⟩).memRead index size).2
        ).withOutput output).world = devm.world := rfl

/-- A `setMach`/`memRead`/`withOutput` return post preserves persistent
storage reads. -/
lemma Devm.retPost_getStorVal (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) (adr : Adr) (key : B256) :
    Devm.getStorVal
        ((((devm.setMach ⟨stack, devm.memory, gas⟩).memRead index size).2
          ).withOutput output) adr key =
      devm.getStorVal adr key := by
  unfold Devm.getStorVal Devm.getAcct
  rw [show (((((devm.setMach ⟨stack, devm.memory, gas⟩).memRead index size).2
      ).withOutput output).state) = devm.state from
        congrArg World.state
          (Devm.retPost_world devm stack gas index size output)]

/-- A `setMach`/`memRead`/`withOutput` return post preserves transient
storage. -/
lemma Devm.retPost_transientStorage (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) :
    ((((devm.setMach ⟨stack, devm.memory, gas⟩).memRead index size).2
        ).withOutput output).transientStorage = devm.transientStorage :=
  congrArg World.transientStorage
    (Devm.retPost_world devm stack gas index size output)

/-- A `setMach`/`memRead`/`withOutput` return post preserves the warmed
storage-key set. -/
lemma Devm.retPost_accessedStorageKeys (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) :
    ((((devm.setMach ⟨stack, devm.memory, gas⟩).memRead index size).2
        ).withOutput output).accessedStorageKeys =
      devm.accessedStorageKeys := by
  rfl

/-- The standard warm/refund/storage-write post has exactly the written
persistent state. -/
lemma Devm.sstoreBase_state (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).state =
        devm.state.setStorVal target key value := rfl

/-- The standard warm/refund/storage-write post preserves the prior error. -/
lemma Devm.sstoreBase_error (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).error = devm.error := rfl

/-- The standard warm/refund/storage-write post preserves transient storage. -/
lemma Devm.sstoreBase_transientStorage
    (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).transientStorage =
        devm.transientStorage := rfl

/-- The standard warm/refund/storage-write post preserves logs. -/
lemma Devm.sstoreBase_logs (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).logs = devm.logs := rfl

/-- The standard warm/refund/storage-write post records exactly the written
storage key in the warmed-key set. -/
lemma Devm.sstoreBase_accessedStorageKeys
    (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).accessedStorageKeys =
        devm.accessedStorageKeys.insert (target, key) := by
  rfl

/-- A warm SSTORE skips the insertion step and therefore preserves the
already-warmed storage-key set across its refund and persistent write. -/
lemma Devm.sstoreWarmBase_accessedStorageKeys
    (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    ((devm.withRefundCounter refund).setStorVal target key value
      ).accessedStorageKeys = devm.accessedStorageKeys := by
  rfl

lemma sstore_getStor_setStorVal {sevm : Sevm} {s s' : Devm} {x xs}
    (h_run : Ninst.Run sevm s Blanc.Ninst.sstore s') (hx : x :: xs <<+ s.stack) :
    ∃ v, Devm.getStor s' sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set x v := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hkx : x = key :=
    (List.of_cons_pref_of_cons_pref hx (pref_of_split (Devm.pop_of_pop h1).stack)).left
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
  have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
  have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  refine ⟨val, ?_⟩
  rw [← eq, setStorVal_getStor_self, hkx, E]

lemma sstore_preserves_stor_rest {x xs} {sevm : Sevm} {s s' : Devm} :
  ¬ ValidAdr x →
  (x :: xs <<+ s.stack) →
  Ninst.Run sevm s Blanc.Ninst.sstore s' →
  (Stor.rest (Devm.getStor s sevm.currentTarget)) = (Stor.rest (Devm.getStor s' sevm.currentTarget)) := by
  intro h_nv h_pfx h_run
  rcases sstore_getStor_setStorVal h_run h_pfx with ⟨v, h_set⟩
  rw [h_set]
  funext a
  have hne : a.toB256 ≠ x := fun hc => h_nv ⟨a, hc⟩
  simp only [Stor.rest, Function.comp_apply]
  rw [Stor.get_set_ne _ hne.symm]

lemma sstore_getStor_set {sevm : Sevm} {s s' : Devm} {x y xs}
    (h_run : Ninst.Run sevm s Blanc.Ninst.sstore s') (hx : x :: y :: xs <<+ s.stack) :
    Devm.getStor s' sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set x y := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hs : s.stack = key :: s₁.stack := (Devm.pop_of_pop h1).stack
  have hs2 : s₁.stack = val :: s₂.stack := (Devm.pop_of_pop h2).stack
  have hxy : x = key ∧ y = val := by
    rw [hs, hs2] at hx
    rcases hx with ⟨sfx, heq⟩
    injection heq with hk hrest
    injection hrest with hv _
    exact ⟨hk.symm, hv.symm⟩
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
  have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
  have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  rw [← eq, setStorVal_getStor_self, hxy.left, hxy.right, E]

syntax "invariance" : tactic
macro_rules
| `(tactic| invariance) =>
  `(tactic| first | apply Line.of_inv _ _ (by assumption); line_inv
                  | apply Func.of_inv _ _ _ (by assumption); func_inv)

lemma of_run_next {fs sevm devm i f devm''}
    (h : Func.Run fs sevm devm (Func.next i f) devm'') :
    ∃ devm', Ninst.Run sevm devm i devm' ∧ Func.Run fs sevm devm' f devm'' := by
  cases h with
  | next h1 h2 => exact ⟨_, h1, h2⟩

/-- Inversion for `Func.call`, as a lemma rather than a `cases` at the use
site: `cases` on `Func.Run` inside a long walk's context generalizes the whole
context against the indices and can diverge in `whnf`, whereas `rcases` on
this existential is cheap. -/
lemma of_run_call {fs : List Func} {sevm : Sevm} {s r : Devm} {k : Nat}
    (h : Func.Run fs sevm s (.call k) r) :
    ∃ f s', fs[k]? = some f ∧ Devm.Burn s s' ∧ Func.Run fs sevm s' f r := by
  cases h with
  | call h_get h_burn h_run => exact ⟨_, _, h_get, h_burn, h_run⟩

/-- A successful conditional whose selected arm calls a known nonreturning
function must take the zero/fall-through arm. -/
theorem of_run_branch_call_of_not_run
    {fs : List Func} {sevm : Sevm} {s r : Devm} {k : Nat}
    {blocked next : Func}
    (hget : fs[k]? = some blocked)
    (blocked_not_run : ∀ {pre post : Devm},
      ¬ Func.Run fs sevm pre blocked post)
    (run : Func.Run fs sevm s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs sevm s' next r := by
  rcases of_run_branch run with
    ⟨s', hpop, hnext⟩ |
    ⟨w, s', s'', hnz, hpop, hburn, hcall⟩
  · exact ⟨s', hpop, hnext⟩
  · rcases of_run_call hcall with
      ⟨f, callPre, hlookup, hcallBurn, hbody⟩
    have hf : f = blocked := by
      rw [hget] at hlookup
      exact Option.some.inj hlookup.symm
    subst f
    exact (blocked_not_run hbody).elim

/-- Successful fall-through past an auxiliary that is exactly `Func.rev`. -/
theorem of_run_branch_call_rev
    {fs : List Func} {sevm : Sevm} {s r : Devm} {k : Nat} {next : Func}
    (hget : fs[k]? = some Func.rev)
    (run : Func.Run fs sevm s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs sevm s' next r := by
  exact of_run_branch_call_of_not_run hget
    (fun hbody => not_run_rev hbody) run

/-! ### `transfer`'s fragments -/

lemma of_transferTestDst {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s transferTestDst s' →
    ∃ na_dst dst,
      ([na_dst, dst] <<+ s'.stack) ∧
      (na_dst = 0 ↔ ValidAdr dst) := by
  simp only [transferTestDst]
  line_execute_with (arg 0)
  rcases prefix_of_cdl nil_pref h₁ with ⟨dst, hp₁⟩
  clear h₁
  line_execute 1
  have hp₂ : [dst, dst] <<+ s₂.stack := by generalize_line_prefix
  clear hp₁ h₂
  intro h
  rcases of_check_non_address hp₂ h with ⟨na_dst, h_pfx, h_iff⟩
  exact ⟨_, _, h_pfx, h_iff⟩

lemma of_transferTestLt {sevm : Sevm} {s s' : Devm} {dst}
    (h_stk : [dst] <<+ s.stack) :
    Line.Run sevm s transferTestLt s' →
    ∃ lt? caller wad,
      ([lt?, caller, Devm.getStorVal s' sevm.currentTarget caller - wad, wad, dst] <<+ s'.stack) ∧
      (lt? = 0 ↔ wad ≤ Devm.getStorVal s' sevm.currentTarget caller) ∧
      ValidAdr caller := by
  simp only [transferTestLt]
  -- arg 1 : push wad
  line_execute_with (arg 1)
  rcases prefix_of_cdl h_stk h₁ with ⟨wad, hp₁⟩
  clear h₁
  -- caller, dup 0 : [caller, caller, wad, dst]
  line_execute 2
  have hp₂ : [sevm.caller.toB256, sevm.caller.toB256, wad, dst] <<+ s₂.stack := by generalize_line_prefix
  clear h₂
  -- sload : [cbal, caller, wad, dst]
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp₂ with ⟨cbal, hp₃, h_cbal⟩
  have hstor23 : Devm.getStor s₂ = Devm.getStor s₃ := Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  -- swap 0, dup 2, dup 0, dup 3, sub, swap 2, lt :
  --   [cbal <? wad, caller, cbal - wad, wad, dst]
  intro h₄
  have hp₄ : [cbal <? wad, sevm.caller.toB256, cbal - wad, wad, dst] <<+ s'.stack := by generalize_line_prefix
  have hstor34 : Devm.getStor s₃ = Devm.getStor s' := Line.of_inv Devm.getStor (by line_inv) h₄
  have h_cbal' : cbal = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [h_cbal]
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s' _).get _
    rw [hstor23, hstor34]
  refine ⟨cbal <? wad, sevm.caller.toB256, wad, ?_, ?_, validAdr_toB256 sevm.caller⟩
  · rw [← h_cbal']; exact hp₄
  · rw [← h_cbal', B256.ltCheck, Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

/-! ### Balance sums do not overflow across a run -/

lemma sum_getBal_state {d : Devm} : sum d.getBal = sum d.state.bal := by
  have h : d.getBal = d.state.bal := funext (fun _ => rfl)
  rw [h]


lemma Exec.preserves_nof {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Exec pc sevm devm exn) :
    ∀ r : Devm, exn = .ok r →
      sum devm.getBal < 2 ^ 256 → sum r.getBal < 2 ^ 256 := by
  intro r h_eq h_nof
  subst h_eq
  exact Nat.lt_of_le_of_lt (Exec.balance_effect run) h_nof

lemma Xinst.preserves_nof {sevm : Sevm} {s r : Devm} {x : Xinst} {xl : Xlot}
    (h : Xinst.Run sevm s x xl (.ok r)) (h_nof : sum s.getBal < 2 ^ 256)
    (h_fill : xl.Filled) :
    sum r.getBal < 2 ^ 256 := by
  have hxl : Xlot.Rel Devm.BalNoninc xl :=
    Xlot.rel_of_filled balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
      Ninst.balance_effectRec Jinst.balance_effect Linst.balance_effect h_fill
  exact Nat.lt_of_le_of_lt (Xinst.balance_effectRec x hxl h) h_nof

lemma Ninst.preserves_nof {sevm : Sevm} {s r : Devm} {i : Ninst}
    (h : Ninst.Run sevm s i r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Ninst.balance_effect i h) h_nof

lemma Func.preserves_nof {c : List Func} {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run c sevm s f r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Func.balance_effect run) h_nof

/-! ## Memory as a byte image

The read/write algebra behind `Mem.Wf`, `Mem.Reads` and `Bytes.writeAt`
(`CommonCore.lean`).  Jaune's `Array.writeD` and `Array.copyD` carry no lemmas
beyond `Array.size_copyD`, so this section starts from their definitions.

Everything here is EVM-generic: no Blanc program, no contract and no ABI shape
appears.  Its consumers are the instruction-level memory images below, and
through them any statement about the bytes a frame hands to an outgoing
`CALL`. -/

lemma Array.size_writeD {ξ : Type} :
    ∀ (ys : List ξ) (xs : Array ξ) (n : Nat),
      (Array.writeD xs n ys).size = xs.size := by
  intro ys
  induction ys with
  | nil => intro xs n; rfl
  | cons y ys ih =>
    intro xs n
    rw [Array.writeD]
    split
    · rw [ih]; simp
    · rfl

lemma Array.getD_set {ξ : Type} (xs : Array ξ) (n : Nat) (y : ξ) (h : n < xs.size)
    (i : Nat) (d : ξ) :
    (xs.set n y h).getD i d = if i = n then y else xs.getD i d := by
  by_cases hi : i = n
  · subst hi; simp [Array.getD, h]
  · simp [Array.getD, Array.getElem_set, hi, Ne.symm hi]

/-- Read-over-write for `Array.writeD`, the primitive behind `Mem.write`.

The hypothesis is what makes the write total: `writeD` silently stops at the end
of the array, and all three of `Mem.write`'s branches arrange for the whole
payload to fit before calling it. -/
lemma Array.getD_writeD {ξ : Type} (d : ξ) :
    ∀ (ys : List ξ) (xs : Array ξ) (n i : Nat), n + ys.length ≤ xs.size →
      (Array.writeD xs n ys).getD i d =
        if n ≤ i ∧ i < n + ys.length then ys.getD (i - n) d else xs.getD i d := by
  intro ys
  induction ys with
  | nil => intro xs n i _; simp [Array.writeD]
  | cons y ys ih =>
    intro xs n i h
    simp only [List.length_cons] at h
    have hn : n < xs.size := by omega
    rw [Array.writeD, dif_pos hn]
    rw [ih (xs.set n y hn) (n + 1) i (by rw [Array.size_set]; omega)]
    rw [Array.getD_set]
    by_cases hi : i = n
    · subst hi
      rw [if_neg (by omega), if_pos rfl, if_pos (by simp), Nat.sub_self]
      rfl
    · by_cases hlt : n ≤ i ∧ i < n + (y :: ys).length
      · have h1 : n + 1 ≤ i ∧ i < n + 1 + ys.length := by
          simp only [List.length_cons] at hlt; omega
        rw [if_pos h1, if_pos hlt]
        have : i - n = (i - (n + 1)) + 1 := by omega
        rw [this]; rfl
      · have h1 : ¬ (n + 1 ≤ i ∧ i < n + 1 + ys.length) := by
          simp only [List.length_cons] at hlt; omega
        rw [if_neg h1, if_neg hlt, if_neg hi]

lemma Array.getD_setIfInBounds {ξ : Type} (a : Array ξ) (k : Nat) (x : ξ)
    (hk : k < a.size) (i : Nat) (d : ξ) :
    (a.setIfInBounds k x).getD i d = if i = k then x else a.getD i d := by
  simp only [Array.setIfInBounds, dif_pos hk]
  exact Array.getD_set a k x hk i d

lemma Array.foldl_setIfInBounds_size {ξ : Type} :
    ∀ (l : List ξ) (a : Array ξ) (k : Nat),
      (List.foldl (fun (ysn : Array ξ × Nat) x =>
        (ysn.fst.setIfInBounds ysn.snd x, ysn.snd + 1)) (a, k) l).fst.size = a.size := by
  intro l
  induction l with
  | nil => intro a k; rfl
  | cons x l ih => intro a k; simp [ih]

lemma Array.foldl_setIfInBounds_getD {ξ : Type} (d : ξ) :
    ∀ (l : List ξ) (a : Array ξ) (k i : Nat), k + l.length ≤ a.size →
      (List.foldl (fun (ysn : Array ξ × Nat) x =>
        (ysn.fst.setIfInBounds ysn.snd x, ysn.snd + 1)) (a, k) l).fst.getD i d =
        if k ≤ i ∧ i < k + l.length then l.getD (i - k) d else a.getD i d := by
  intro l
  induction l with
  | nil => intro a k i _; simp
  | cons x l ih =>
    intro a k i h
    simp only [List.length_cons] at h
    have hk : k < a.size := by omega
    simp only [List.foldl_cons]
    rw [ih (a.setIfInBounds k x) (k + 1) i
      (by rw [Array.size_setIfInBounds]; omega)]
    rw [Array.getD_setIfInBounds a k x hk]
    by_cases hi : i = k
    · subst hi
      rw [if_neg (by omega), if_pos rfl, if_pos (by simp), Nat.sub_self]
      rfl
    · by_cases hlt : k ≤ i ∧ i < k + (x :: l).length
      · have h1 : k + 1 ≤ i ∧ i < k + 1 + l.length := by
          simp only [List.length_cons] at hlt; omega
        rw [if_pos h1, if_pos hlt]
        have hsub : i - k = (i - (k + 1)) + 1 := by omega
        rw [hsub]; rfl
      · have h1 : ¬ (k + 1 ≤ i ∧ i < k + 1 + l.length) := by
          simp only [List.length_cons] at hlt; omega
        rw [if_neg h1, if_neg hlt, if_neg hi]

/-- Read-back for `Array.copyD`, whose contract is "overwrite the front of `ys`
with `xs`, keeping `ys`'s length".  With `xs` no longer than `ys` nothing is
dropped, which is the only case `Mem.write` ever creates. -/
lemma Array.getD_copyD {ξ : Type} (xs ys : Array ξ) (d : ξ) (h : xs.size ≤ ys.size)
    (i : Nat) :
    (Array.copyD xs ys).getD i d = if i < xs.size then xs.getD i d else ys.getD i d := by
  simp only [Array.copyD]
  rw [← Array.foldl_toList]
  rw [Array.foldl_setIfInBounds_getD d xs.toList ys 0 i (by simpa using h)]
  by_cases hi : i < xs.size
  · rw [if_pos (by simpa using hi), if_pos hi, Nat.sub_zero]
    simp [Array.getD, hi]
  · rw [if_neg (by simpa using hi), if_neg hi]

/-! ### The list side of `Bytes.writeAt` -/

lemma List.getD_append_left {ξ : Type} {l₁ l₂ : List ξ} {i : Nat} (d : ξ)
    (h : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma List.getD_append_right {ξ : Type} {l₁ l₂ : List ξ} {i : Nat} (d : ξ)
    (h : l₁.length ≤ i) : (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma List.getD_drop {ξ : Type} (l : List ξ) (k j : Nat) (d : ξ) :
    (l.drop k).getD j d = l.getD (k + j) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma List.getD_takeD {ξ : Type} (d : ξ) :
    ∀ (n : Nat) (l : List ξ) (i : Nat),
      (List.takeD n l d).getD i d = if i < n then l.getD i d else d := by
  intro n
  induction n with
  | zero => intro l i; simp
  | succ n ih =>
    intro l i
    rw [List.takeD_succ]
    cases i with
    | zero => cases l <;> simp
    | succ i =>
      rw [show ((l.head?.getD d :: List.takeD n l.tail d).getD (i + 1) d)
            = (List.takeD n l.tail d).getD i d from rfl, ih l.tail i]
      by_cases hi : i < n
      · rw [if_pos hi, if_pos (by omega)]
        cases l <;> simp
      · rw [if_neg hi, if_neg (by omega)]

lemma List.takeD_nil_eq_replicate {ξ} (d : ξ) :
    ∀ n, List.takeD n ([] : List ξ) d = List.replicate n d := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show ([] : List ξ).head?.getD d :: List.takeD n ([] : List ξ).tail d = _
    rw [show ([] : List ξ).tail = [] from rfl, ih]; rfl

/-- Taking *more* than there is pads with the default.

The half of `List.takeD` that `List.takeD_eq_take` does not cover, and the shape
a `CALL`'s argument window takes when it runs past the bytes the frame actually
wrote: `Mem.Reads` compares with `getD` on both sides, so those trailing
positions read as `0`, which is exactly `abiBytesTail`'s zero padding. -/
lemma List.takeD_of_length_le {ξ} (d : ξ) :
    ∀ (l : List ξ) (n : Nat), l.length ≤ n →
      List.takeD n l d = l ++ List.replicate (n - l.length) d := by
  intro l
  induction l with
  | nil => intro n _; rw [List.takeD_nil_eq_replicate]; simp
  | cons a l ih =>
    intro n hn
    cases n with
    | zero => simp at hn
    | succ m =>
      have hm : l.length ≤ m := by simp at hn; omega
      show (a :: l).head?.getD d :: List.takeD m ((a :: l).tail) d = _
      rw [show (a :: l).tail = l from rfl, ih m hm]
      simp

/-- `Bytes.writeAt` read pointwise: inside the written range it is the payload,
outside it is the old image.  Every `Mem.Reads` step below is this equation
paired with `Array.getD_writeD`. -/
lemma Bytes.getD_writeAt (bs : Bytes) (n : Nat) (xs : Bytes) (i : Nat) :
    (Bytes.writeAt bs n xs).getD i 0 =
      if n ≤ i ∧ i < n + xs.length then xs.getD (i - n) 0 else bs.getD i 0 := by
  simp only [Bytes.writeAt, List.append_assoc]
  have hlen : (List.takeD n bs 0).length = n := List.takeD_length n bs 0
  by_cases h1 : i < n
  · rw [List.getD_append_left 0 (by omega), List.getD_takeD, if_pos h1,
      if_neg (by omega)]
  · rw [List.getD_append_right 0 (by omega), hlen]
    by_cases h2 : i < n + xs.length
    · rw [List.getD_append_left 0 (by omega), if_pos ⟨by omega, h2⟩]
    · rw [List.getD_append_right 0 (by omega), if_neg (by omega),
        List.getD_drop]
      congr 1
      omega

/-- Taking a padded slice from zero at the exact source length returns the
source unchanged. -/
lemma Bytes.sliceD_zero_length {bs : Bytes} {n : Nat}
    (h : bs.length = n) : bs.sliceD 0 n 0 = bs := by
  unfold List.sliceD
  simp only [List.drop_zero]
  rw [List.takeD_eq_take _ (by omega), ← h]
  exact List.take_length

/-- Split a padded slice at an arbitrary width.  This is the list-level
identity used when adjacent ABI words are proved separately and then
reassembled into one event or call-data window. -/
lemma List.sliceD_split {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d =
        xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero => intro m b; simp [List.sliceD, List.takeD]
  | succ a ih =>
      intro m b
      rw [show a + 1 + b = (a + b) + 1 by omega, List.sliceD_succ,
        ih (m + 1) b, List.sliceD_succ xs m a d,
        show m + (a + 1) = m + 1 + a by omega]
      rfl

/-- Writing at the end of the image is an append.  The shape every store in a
frame that lays memory out once, upward and without gaps, takes. -/
lemma Bytes.writeAt_length (bs xs : Bytes) :
    Bytes.writeAt bs bs.length xs = bs ++ xs := by
  rw [Bytes.writeAt, List.takeD_eq_take _ (Nat.le_refl _), List.take_length,
    List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.append_nil]

/-- `Bytes.writeAt_length` with the offset given as a numeral.  A walk meets the
append shape as `writeAt bs 96 xs`, never as `writeAt bs bs.length xs`, and
rewriting a numeral into a `length` first is what makes those two the same
step. -/
lemma Bytes.writeAt_of_length_eq {bs xs : Bytes} {n : Nat} (h : bs.length = n) :
    Bytes.writeAt bs n xs = bs ++ xs := by
  subst h; exact Bytes.writeAt_length bs xs

/-- Writing over the whole image from `0` replaces it.  The other shape: the
mint's `Transfer` data lands at `0`, and `storeCallbackHead`'s first store lands
on top of it. -/
lemma Bytes.writeAt_zero_of_le {bs xs : Bytes} (h : bs.length ≤ xs.length) :
    Bytes.writeAt bs 0 xs = xs := by
  rw [Bytes.writeAt, show List.takeD 0 bs 0 = [] from rfl, List.nil_append,
    List.drop_eq_nil_of_le (by omega), List.append_nil]

/-- Reading a write back at its own offset returns the payload.  The read-back
step of every store-then-load fragment: `checkRetdataHead` clobbers a memory
word and immediately `MLOAD`s it. -/
lemma Bytes.sliceD_writeAt (bs xs : Bytes) (n : Nat) :
    (Bytes.writeAt bs n xs).sliceD n xs.length 0 = xs := by
  unfold List.sliceD
  rw [Bytes.writeAt, List.append_assoc,
    List.drop_append_of_le_length (by rw [List.takeD_length]),
    List.drop_eq_nil_of_le (by rw [List.takeD_length]), List.nil_append,
    List.takeD_eq_take _ (by simp), List.take_left]

/-! ### `Mem.Wf` and `Mem.Reads` -/

lemma Nat.le_mul_ceilDiv (n m : Nat) (hm : 0 < m) : n ≤ m * ceilDiv n m := by
  simp only [ceilDiv]
  have hdm := Nat.div_add_mod n m
  rcases Nat.eq_zero_or_pos (n % m) with h | h
  · rw [if_pos h, Nat.add_zero]
    omega
  · rw [if_neg (by omega), Nat.mul_add, Nat.mul_one]
    have := Nat.mod_lt n hm
    omega

lemma Mem.wf_empty : Mem.Wf Mem.empty := Nat.le_refl 0

lemma Mem.reads_empty : Mem.Reads Mem.empty [] := fun _ => rfl

lemma Mem.Wf.extend {μ : Mem} (h : Mem.Wf μ) (index size : Nat) :
    Mem.Wf (μ.extend index size) := by
  simp only [Mem.Wf, Mem.extend] at *
  simp only [memExtSize]
  split
  · exact h
  · have h1 : μ.size ≤ 32 * ceilDiv μ.size 32 :=
      Nat.le_mul_ceilDiv μ.size 32 (by omega)
    have hmax : 32 * ceilDiv μ.size 32
        ≤ 32 * max (ceilDiv μ.size 32) (ceilDiv (index + size) 32) :=
      Nat.mul_le_mul_left 32 (Nat.le_max_left _ _)
    omega

lemma Mem.Wf.extends : ∀ (pairs : List (Nat × Nat)) {μ : Mem},
    Mem.Wf μ → Mem.Wf (μ.extends pairs) := by
  intro pairs
  induction pairs with
  | nil => intro μ h; exact h
  | cons p ps ih =>
    rcases p with ⟨idx, sz⟩
    intro μ h
    exact ih (Mem.Wf.extend h idx sz)

lemma Mem.Reads.extend {μ : Mem} {bs : Bytes} (h : Mem.Reads μ bs)
    (index size : Nat) : Mem.Reads (μ.extend index size) bs := h

lemma Mem.Reads.extends : ∀ (pairs : List (Nat × Nat)) {μ : Mem} {bs : Bytes},
    Mem.Reads μ bs → Mem.Reads (μ.extends pairs) bs := by
  intro pairs
  induction pairs with
  | nil => intro μ bs h; exact h
  | cons p ps ih =>
    rcases p with ⟨idx, sz⟩
    intro μ bs h
    exact ih (Mem.Reads.extend h idx sz)

lemma Nat.le_ceil32 (n : Nat) : n ≤ ceil32 n := by
  unfold ceil32
  split
  · exact Nat.le_refl _
  · rename_i m hm
    have := Nat.mod_lt n (show 0 < 32 by omega)
    omega

lemma Array.getD_replicate_zero (k i : Nat) :
    (Array.replicate k (0 : UInt8)).getD i 0 = 0 := by
  simp [Array.getD]

lemma Array.getD_of_size_le {ξ : Type} {xs : Array ξ} {i : Nat} (d : ξ)
    (h : xs.size ≤ i) : xs.getD i d = d := by
  simp [Array.getD, Nat.not_lt.mpr h]

/-- `Mem.write`'s three branches, factored.

Whichever branch it takes, the result is `Array.writeD` over an array that reads
exactly as the old one, is long enough to hold the whole payload, and does not
run past the new logical size.  The `Mem.Wf` hypothesis is precisely what rules
out the truncation `Array.copyD` would otherwise perform in the growth branch,
where the fresh array is `ceil32 (n + ys.length)` long. -/
lemma Mem.write_aux {μ : Mem} (hwf : Mem.Wf μ) (n : Nat) :
    ∀ {ys : Bytes}, ys ≠ [] →
      ∃ A : Array UInt8,
        (μ.write n ys).data = Array.writeD A n ys ∧
        n + ys.length ≤ A.size ∧
        A.size ≤ (μ.write n ys).size ∧
        ∀ i, A.getD i 0 = μ.data.getD i 0 := by
  intro ys hne
  cases ys with
  | nil => exact absurd rfl hne
  | cons y ys =>
    simp only [Mem.Wf] at hwf
    simp only [Mem.write]
    by_cases h1 : n + (y :: ys).length ≤ μ.size
    · rw [if_pos h1]
      by_cases h2 : n + (y :: ys).length ≤ μ.data.size
      · rw [if_pos h2]
        exact ⟨μ.data, rfl, h2, hwf, fun _ => rfl⟩
      · rw [if_neg h2]
        refine ⟨Array.copyD μ.data
          (Array.replicate (n + (y :: ys).length) 0x00), rfl, ?_, ?_, ?_⟩
        · rw [Array.size_copyD, Array.size_replicate]
        · rw [Array.size_copyD, Array.size_replicate]; exact h1
        · intro i
          rw [Array.getD_copyD _ _ _ (by rw [Array.size_replicate]; omega)]
          by_cases hi : i < μ.data.size
          · rw [if_pos hi]
          · rw [if_neg hi, Array.getD_replicate_zero,
              Array.getD_of_size_le 0 (Nat.not_lt.mp hi)]
    · rw [if_neg h1]
      have hle : n + (y :: ys).length ≤ ceil32 (n + (y :: ys).length) :=
        Nat.le_ceil32 _
      refine ⟨Array.copyD μ.data
        (Array.replicate (ceil32 (n + (y :: ys).length)) 0x00), rfl, ?_, ?_, ?_⟩
      · rw [Array.size_copyD, Array.size_replicate]; exact hle
      · rw [Array.size_copyD, Array.size_replicate]
      · intro i
        rw [Array.getD_copyD _ _ _ (by rw [Array.size_replicate]; omega)]
        by_cases hi : i < μ.data.size
        · rw [if_pos hi]
        · rw [if_neg hi, Array.getD_replicate_zero,
            Array.getD_of_size_le 0 (Nat.not_lt.mp hi)]

lemma Mem.Wf.write {μ : Mem} (h : Mem.Wf μ) (n : Nat) (ys : Bytes) :
    Mem.Wf (μ.write n ys) := by
  cases ys with
  | nil => exact h
  | cons y ys =>
    rcases Mem.write_aux h n (ys := y :: ys) (by simp) with ⟨A, hdata, _, hsz, _⟩
    simp only [Mem.Wf, hdata, Array.size_writeD]
    exact hsz

/-- Read-over-write for EVM memory, and the whole point of this section: the
image after a write is the image before it with the payload laid over it, and
everything the write did not touch — including the bytes past the payload inside
the word the machine rounds up to — still reads as it did. -/
lemma Mem.Reads.write {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (h : Mem.Reads μ bs)
    (n : Nat) (ys : Bytes) :
    Mem.Reads (μ.write n ys) (Bytes.writeAt bs n ys) := by
  cases ys with
  | nil =>
    intro i
    rw [Bytes.getD_writeAt]
    simp only [List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]
    exact h i
  | cons y ys =>
    rcases Mem.write_aux hwf n (ys := y :: ys) (by simp) with
      ⟨A, hdata, hlen, _, hreads⟩
    intro i
    rw [hdata, Array.getD_writeD 0 _ A n i hlen, Bytes.getD_writeAt]
    by_cases hin : n ≤ i ∧ i < n + (y :: ys).length
    · rw [if_pos hin, if_pos hin]
    · rw [if_neg hin, if_neg hin, hreads i]
      exact h i

/-! ### Reading the image back

`Mem.read` slices the backing array with `Array.sliceD`, which accumulates from
the far end, while `List.sliceD` consumes from the near end.  Both are put in
the same `List.range` normal form, after which a pointwise `Mem.Reads` transfers
between them. -/

lemma Array.sliceD_aux_eq {ξ : Type} (xs : Array ξ) (d : ξ) :
    ∀ (n : Nat) (Acc : List ξ) (m : Nat),
      Array.sliceD.aux xs Acc m n d
        = (List.range n).map (fun j => xs.getD (m + j) d) ++ Acc := by
  intro n
  induction n with
  | zero => intro Acc m; rfl
  | succ n ih =>
    intro Acc m
    rw [show Array.sliceD.aux xs Acc m (n + 1) d
          = Array.sliceD.aux xs (xs.getD (m + n) d :: Acc) m n d from rfl,
      ih, List.range_succ]
    simp

lemma Array.sliceD_eq_map {ξ : Type} (xs : Array ξ) (m n : Nat) (d : ξ) :
    Array.sliceD xs m n d = (List.range n).map (fun j => xs.getD (m + j) d) := by
  rw [show Array.sliceD xs m n d = Array.sliceD.aux xs [] m n d from rfl,
    Array.sliceD_aux_eq]
  simp

lemma List.sliceD_eq_map {ξ : Type} (ys : List ξ) (d : ξ) :
    ∀ (n m : Nat), List.sliceD ys m n d
      = (List.range n).map (fun j => ys.getD (m + j) d) := by
  intro n
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
    intro m
    rw [List.sliceD_succ, ih (m + 1), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    show ys.getD (m + 1 + j) d = ys.getD (m + (j + 1)) d
    rw [show m + (j + 1) = m + 1 + j from by omega]

/-- Pointwise read inside a padded slice, while the requested index remains
inside that slice's declared width. -/
lemma Bytes.getD_sliceD_of_lt
    (bs : Bytes) (start len i : Nat) (hi : i < len) :
    (bs.sliceD start len 0).getD i 0 = bs.getD (start + i) 0 := by
  rw [List.sliceD_eq_map]
  simp [List.getD_eq_getElem?_getD, hi]

/-- A subwindow wholly inside a padded slice is the corresponding slice of the
original image.  This is the word-projection rule for a multiword ABI copy. -/
lemma Bytes.sliceD_sliceD_of_le
    (bs : Bytes) (start width offset len : Nat)
    (h : offset + len ≤ width) :
    (bs.sliceD start width 0).sliceD offset len 0 =
      bs.sliceD (start + offset) len 0 := by
  rw [List.sliceD_eq_map (bs.sliceD start width 0) 0 len offset,
    List.sliceD_eq_map bs 0 len (start + offset)]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega)]
  congr 1
  omega

/-- A write starting after a requested slice leaves that earlier slice
unchanged. -/
lemma Bytes.sliceD_writeAt_before
    (bs xs : Bytes) (start len n : Nat)
    (h : start + len ≤ n) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [if_neg]
  omega

/-- The mirror of `Bytes.sliceD_writeAt_before`: a write that lands entirely
below the read window leaves it alone.  Scratch-word walks need both halves,
because later writes may sit on either side of an earlier word. -/
lemma Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [if_neg]
  omega

/-- A padded read wholly inside a written window reads the corresponding
subwindow of the payload.  Constructor decoders use this after copying a
multiword ABI head and then loading its individual words. -/
lemma Bytes.sliceD_writeAt_inside
    (bs xs : Bytes) (n start len : Nat)
    (hstart : n ≤ start) (hend : start + len ≤ n + xs.length) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      xs.sliceD (start - n) len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt, if_pos (by omega)]
  congr 1
  omega

/-- Reading back the 32-byte word just written at `n`.  Scratch-word walks
store and reload whole words, so this is the shape they need rather than the
length-polymorphic `Bytes.sliceD_writeAt`. -/
lemma Bytes.readWord_writeAt_self (bs : Bytes) (n : Nat) (v : B256) :
    Bytes.toB256 ((Bytes.writeAt bs n v.toBytes).sliceD n 32 0) = v := by
  rw [show (32 : Nat) = v.toBytes.length from (B256.length_toBytes v).symm,
    Bytes.sliceD_writeAt]
  exact B256.toB256_toBytes v

/-- A 32-byte word write that misses the 32-byte read window entirely, on
either side, leaves it alone. -/
lemma Bytes.readWord_writeAt_of_disjoint (bs : Bytes) (start n : Nat)
    (v : B256) (h : start + 32 ≤ n ∨ n + 32 ≤ start) :
    (Bytes.writeAt bs n v.toBytes).sliceD start 32 0 =
      bs.sliceD start 32 0 := by
  rcases h with h | h
  · exact Bytes.sliceD_writeAt_before bs v.toBytes start 32 n h
  · exact Bytes.sliceD_writeAt_after bs v.toBytes start 32 n
      (by rw [B256.length_toBytes]; exact h)

/-- What a `CALL`, `LOG` or `MLOAD` reads out of a memory whose image is known:
exactly the corresponding slice of the image, zero-padded past its end. -/
lemma Mem.Reads.read {μ : Mem} {bs : Bytes} (h : Mem.Reads μ bs) (i n : Nat) :
    (μ.read i n).1 = bs.sliceD i n 0 := by
  show Array.sliceD μ.data i n 0 = _
  rw [Array.sliceD_eq_map, List.sliceD_eq_map]
  exact List.map_congr_left (fun j _ => h (i + j))

/-- Two adjacent whole-word writes determine their 64-byte image window. -/
lemma Bytes.read_two_word_writes_at (image : Bytes) (start : Nat)
    (left right : B256) :
    (Bytes.writeAt (Bytes.writeAt image start left.toBytes)
      (start + 32) right.toBytes).sliceD start 64 0 =
        left.toBytes ++ right.toBytes := by
  rw [show (64 : Nat) = 32 + 32 by omega, List.sliceD_split]
  congr 1
  · rw [Bytes.sliceD_writeAt_before _ _ start 32 (start + 32) (by omega),
      show (32 : Nat) = left.toBytes.length from
        (B256.length_toBytes left).symm,
      Bytes.sliceD_writeAt]
  · rw [show (32 : Nat) = right.toBytes.length from
        (B256.length_toBytes right).symm,
      Bytes.sliceD_writeAt]

/-- Two adjacent whole-word stores at an arbitrary memory offset determine the
complete 64-byte readback independently of the prior image.  `Mem.Wf` is
needed only to transport the reader image through the two writes. -/
lemma Mem.read_two_word_writes_at {μ : Mem} {image : Bytes}
    (hwf : Mem.Wf μ) (hreads : Mem.Reads μ image) (start : Nat)
    (left right : B256) :
    ((((μ.write start left.toBytes).write (start + 32) right.toBytes).read
      start 64).1) =
      left.toBytes ++ right.toBytes := by
  have hreadsLeft : Mem.Reads (μ.write start left.toBytes)
      (Bytes.writeAt image start left.toBytes) :=
    Mem.Reads.write hwf hreads start left.toBytes
  have hreadsRight :
      Mem.Reads
        ((μ.write start left.toBytes).write (start + 32) right.toBytes)
        (Bytes.writeAt (Bytes.writeAt image start left.toBytes)
          (start + 32) right.toBytes) :=
    Mem.Reads.write (Mem.Wf.write hwf start left.toBytes) hreadsLeft
      (start + 32) right.toBytes
  rw [Mem.Reads.read hreadsRight,
    Bytes.read_two_word_writes_at]

/-- Offset-zero specialization retained for existing event proofs. -/
lemma Mem.read_two_word_writes {μ : Mem} {image : Bytes}
    (hwf : Mem.Wf μ) (hreads : Mem.Reads μ image) (left right : B256) :
    ((((μ.write 0 left.toBytes).write 32 right.toBytes).read 0 64).1) =
      left.toBytes ++ right.toBytes := by
  simpa using Mem.read_two_word_writes_at hwf hreads 0 left right

/-- Reading back a nonempty byte string immediately after writing it at offset
zero returns that byte string, independently of the old memory image.  Unlike
`Mem.Reads.write`, this self-window fact needs no well-formedness premise: each
branch of `Mem.write` allocates enough backing array for the payload itself. -/
lemma Mem.read_write_zero (μ : Mem) {ys : Bytes} (hne : ys ≠ []) :
    ((μ.write 0 ys).read 0 ys.length).1 = ys := by
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp only [Mem.write]
    split
    · split
      · simp only [Mem.read, Array.sliceD_eq_map]
        apply List.ext_get
        · simp
        · intro n h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp only [List.get_eq_getElem, List.getElem_map,
            List.getElem_range, zero_add]
          rw [Array.getD_writeD 0 (b :: bs) μ.data 0 n (by omega),
            if_pos (by omega)]
          simp [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem h2]
      · simp only [Mem.read, Array.sliceD_eq_map]
        apply List.ext_get
        · simp
        · intro n h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp only [List.get_eq_getElem, List.getElem_map,
            List.getElem_range, zero_add]
          rw [Array.getD_writeD 0 (b :: bs)
            (Array.copyD μ.data (Array.replicate (b :: bs).length 0))
            0 n (by simp [Array.size_copyD]), if_pos (by omega)]
          simp [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem h2]
    · simp only [Mem.read, Array.sliceD_eq_map]
      apply List.ext_get
      · simp
      · intro n h1 h2
        simp only [List.length_map, List.length_range] at h1
        simp only [List.get_eq_getElem, List.getElem_map,
          List.getElem_range, zero_add]
        rw [Array.getD_writeD 0 (b :: bs)
          (Array.copyD μ.data
            (Array.replicate (ceil32 (b :: bs).length) 0))
          0 n (by
            rw [Array.size_copyD, Array.size_replicate]
            simpa using Nat.le_ceil32 (b :: bs).length),
          if_pos (by omega)]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h2]

/-! ### What memory a written instruction writes

The `Hinv Devm.memory` instance family that carries a memory image across a
memory-silent `Line` sits earlier in this file, beside its `Devm.state` /
`Devm.getStor` / `Devm.getCode` siblings — dispatch reachability needs it too,
and instance resolution is position-sensitive within a module.  What follows is
the other half: value-carrying inversions for the three instructions that do
touch memory, in the same shape Step 1 gave `calldataload` and `calldatacopy` —
what was written, and where. -/

/-- `MSTORE` writes *the word it popped* at *the offset it popped*.

The value-carrying companion of `of_run_mstore`, and the first Blanc lemma whose
conclusion names `Devm.memory` at all. -/
lemma of_run_mstore_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat y.toBytes := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hmem : s.memory = s₃.memory := (p1.memory.trans p2.memory).trans hb.memory
  refine ⟨x, v, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 p2).stack
    rw [← eq, show (Devm.memWrite s₃ x.toNat v.toBytes).stack = s₃.stack from rfl,
      ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `MSTORE8` writes the low byte of the word it popped at the offset it
popped.  This is the byte-store companion of `of_run_mstore_val`. -/
lemma of_run_mstore8_val {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mstore8 s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat [y.2.2.toUInt8] := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hmem : s.memory = s₃.memory :=
    (p1.memory.trans p2.memory).trans hb.memory
  refine ⟨x, v, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 p2).stack
    rw [← eq,
      show (Devm.memWrite s₃ x.toNat [v.2.2.toUInt8]).stack =
        s₃.stack from rfl,
      ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- A successful `MSTORE8` changes only the machine-local frame, not the
persistent world state. -/
lemma of_run_mstore8_state {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mstore8 s') : s.state = s'.state := by
  rcases of_run_reg h with ⟨pc, run⟩
  have frame := Rinst.run_instructionFrame pc e s .mstore8
    (by intro equal; cases equal) (by intro equal; cases equal)
  rw [run] at frame
  exact frame.state

/-- `CALLDATACOPY` writes *the calldata slice named by its operands* at *the
offset it popped*, and touches nothing else.

Strengthens `of_run_calldatacopy_val` (Step 1), which named the bytes but could
not relate the intermediate state's memory to the initial one — there was no
`Mem` algebra to say it in. -/
lemma of_run_calldatacopy_mem {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat (e.data.sliceD y.toNat z.toNat 0) := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  refine ⟨x, y, z, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq, show (Devm.memWrite s₄ x.toNat _).stack = s₄.stack from rfl, ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `CODECOPY` writes the exact code-image slice named by its three operands at
the popped destination offset.  This is the creation-code companion of
`of_run_calldatacopy_mem`. -/
lemma of_run_codecopy_mem {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s codecopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat
        (e.code.sliceD y.toNat z.toNat (Linst.toUInt8 .stop)) := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨ci, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  refine ⟨x, y, z, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq,
      show (Devm.memWrite s₄ x.toNat _).stack = s₄.stack from rfl,
      ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `CODECOPY` is log-silent.  Like `MLOAD`, it has no global `Ninst.Hinv`
instance for logs, so constructor-return proofs use this exact successful-run
fact instead of assuming a broader instruction class. -/
lemma of_run_codecopy_logs {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s codecopy s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨_, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨_, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨_, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨_, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨_, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨_, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨_, p3⟩
  have burned := Devm.burn_of_chargeGas h4
  injection h5 with stateEq
  rw [← stateEq]
  exact ((p1.logs.trans p2.logs).trans p3.logs).trans burned.logs

/-- `LOG` only *extends* memory: it reads a window and records it, and the
backing array is untouched.  That is enough to carry both `Mem.Wf` and a
`Mem.Reads` image across the mint's `Transfer` event. -/
lemma of_run_log_mem {e : Sevm} {s s' : Devm} {n : Fin 5}
    (h : Ninst.Run e s (log n) s') :
    ∃ mi sz, s'.memory = s.memory.extend mi sz := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨_, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  refine ⟨mi, sz, ?_⟩
  rcases h_mem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_s₅ : s₅.memory = s₄.memory.extend mi sz := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]
    show mem = _
    have hm2 : mem = (s₄.memory.read mi sz).2 := by rw [h_read]
    rw [hm2]
    rfl
  rw [← eq]
  show s₅.memory = _
  rw [h_s₅, hmem]

/-- Value-carrying memory companion for `LOG`.  The popped offset/size and
topics are shared with the stack relation, so fixed-shape fragments can pin the
exact memory extension without reopening `Rinst.runCore`. -/
lemma of_run_log_mem_val {e : Sevm} {s s' : Devm} {n : Fin 5}
    (h : Ninst.Run e s (log n) s') :
    ∃ mi sz topics,
      topics.length = n.val ∧
      Stack.Pop (mi :: sz :: topics) s.stack s'.stack ∧
      s'.memory = s.memory.extend mi.toNat sz.toNat := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popN h3 with ⟨hlen, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases hmem : Devm.memRead s₄ x.toNat y.toNat with ⟨data, s₅⟩
  rw [hmem] at run₅
  injection run₅ with eq
  have hpre : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  have hstack : s₅.stack = s₄.stack := by
    have hs := Devm.memRead_stack s₄ x.toNat y.toNat
    rw [hmem] at hs
    exact hs
  have hmemory : s₅.memory = s₄.memory.extend x.toNat y.toNat := by
    simp only [Devm.memRead] at hmem
    rcases hread : s₄.memory.read x.toNat y.toNat with ⟨val, mem⟩
    rw [hread] at hmem
    injection hmem with _ hdevm
    rw [← hdevm]
    show mem = _
    have hm : mem = (s₄.memory.read x.toNat y.toNat).2 := by rw [hread]
    rw [hm]
    rfl
  refine ⟨x, y, topics, hlen, ?_, ?_⟩
  · rw [← eq]
    show Stack.Pop (x :: y :: topics) s.stack s₅.stack
    rw [hstack, ← hb.stack]
    exact (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  · rw [← eq]
    show s₅.memory = _
    rw [hmemory, hpre]

/-- `MSTORE` at a *known* stack top: the value-carrying companion of
`prefix_of_mstore`, with the popped operands pinned to the words the walk
already knows are there. -/
lemma prefix_of_mstore_val {e} {x y xs} {s s' : Devm}
    (h0 : Ninst.Run e s mstore s') (h1 : x :: y :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧ s'.memory = s.memory.write x.toNat y.toBytes := by
  rcases of_run_mstore_val h0 with ⟨x', y', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, -⟩
  refine ⟨?_, by rw [hx, hy]; exact hm⟩
  rw [hx, hy] at h1
  exact of_append_pref h2 h1

/-- `MSTORE8` at a known stack top, retaining the exact low-byte write. -/
lemma prefix_of_mstore8_val {e} {x y xs} {s s' : Devm}
    (h0 : Ninst.Run e s mstore8 s')
    (h1 : x :: y :: xs <<+ s.stack) :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write x.toNat [y.2.2.toUInt8] := by
  rcases of_run_mstore8_val h0 with ⟨x', y', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, -⟩
  refine ⟨?_, by rw [hx, hy]; exact hm⟩
  rw [hx, hy] at h1
  exact of_append_pref h2 h1

/-- Every successful `mstoreAt` run begins with the word it consumes at the
head of the input stack. -/
theorem mstoreAt_stack_head
    {e : Sevm} {pre post : Devm} {k : B256}
    (run : Line.Run e pre (mstoreAt k) post) :
    ∃ word tail, word :: tail <<+ pre.stack := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨afterPush, hpush, run⟩
  rcases Line.of_run_cons run with ⟨afterStore, hstore, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 hpush
  rcases of_run_mstore hstore with ⟨offset, word, hpop⟩
  have hstack : (k * 32) :: pre.stack =
      offset :: word :: post.stack :=
    pushed.stack.symm.trans hpop
  injection hstack with hoff htail
  refine ⟨word, post.stack, ?_⟩
  rw [htail]
  simpa using (pref_append (word :: post.stack) [])

/-- `mstoreAt k` writes the stack top into memory word `k`.

The `Line`-level form, and the one every `storeCallbackHead`-shaped fragment
composes: `(k * 32).toNat` is the byte offset the compiled `PUSH` supplies, and
`B256.toBytes` is the machine's own 32-byte big-endian encoding. -/
lemma of_run_mstoreAt_val {e : Sevm} {s s' : Devm} {k x xs}
    (h : Line.Run e s (mstoreAt k) s') (hp : x :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧ s'.memory = s.memory.write (k * 32).toNat x.toBytes := by
  rcases Line.of_run_cons h with ⟨u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  rcases prefix_of_mstore_val qm (prefix_of_push hpb hp) with ⟨hs, hm⟩
  exact ⟨hs, by rw [hm, ← hpb.memory]⟩

/-- A fixed-word `MSTORE` step with the proof-carrying memory image advanced
in lockstep.  This is the shared scratch-decoder wrapper around
`of_run_mstoreAt_val`, `Mem.Wf.write`, and `Mem.Reads.write`. -/
theorem of_run_mstoreAt_image
    {e : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : value :: tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (run : Line.Run e pre (mstoreAt word) post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image (word * 32).toNat value.toBytes) ∧
      pre.state = post.state := by
  obtain ⟨stack, memory⟩ := of_run_mstoreAt_val run hp
  refine ⟨stack, ?_, ?_, Line.of_inv Devm.state (by line_inv) run⟩
  · rw [memory]
    exact hwf.write _ _
  · rw [memory]
    exact Mem.Reads.write hwf hreads _ _

/-- `CALLDATACOPY` at a *known* stack top: the value-carrying companion of
`prefix_of_calldatacopy`, with the three popped operands pinned to the words the
walk already knows are there. -/
lemma prefix_of_calldatacopy_val {e} {x y z xs} {s s' : Devm}
    (h0 : Ninst.Run e s calldatacopy s') (h1 : x :: y :: z :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧
      s'.memory = s.memory.write x.toNat (e.data.sliceD y.toNat z.toNat 0) := by
  rcases of_run_calldatacopy_mem h0 with ⟨x', y', z', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, -⟩
  refine ⟨?_, by rw [hx, hy, hz]; exact hm⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- `CODECOPY` at a known stack top, retaining the exact written code slice. -/
lemma prefix_of_codecopy_val {e} {x y z xs} {s s' : Devm}
    (h0 : Ninst.Run e s codecopy s') (h1 : x :: y :: z :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧
      s'.memory = s.memory.write x.toNat
        (e.code.sliceD y.toNat z.toNat (Linst.toUInt8 .stop)) := by
  rcases of_run_codecopy_mem h0 with ⟨x', y', z', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, -⟩
  refine ⟨?_, by rw [hx, hy, hz]; exact hm⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- Exact proof-carrying image update for a successful `CODECOPY`.  Besides the
three-word stack burn, this retains memory well-formedness, the updated image,
and the persistent-state/log frame needed to compose constructor decoders. -/
theorem of_run_codecopy_image
    {e : Sevm} {pre post : Devm} {dst src size : B256}
    {tail : Stack} {image : Bytes}
    (hp : dst :: src :: size :: tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (run : Ninst.Run e pre codecopy post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image dst.toNat
          (e.code.sliceD src.toNat size.toNat (Linst.toUInt8 .stop))) ∧
      pre.state = post.state ∧
      pre.logs = post.logs := by
  obtain ⟨pstack, memory⟩ := prefix_of_codecopy_val run hp
  refine ⟨pstack, ?_, ?_, Ninst.Hinv.inv run, of_run_codecopy_logs run⟩
  · rw [memory]
    exact Mem.Wf.write hwf _ _
  · rw [memory]
    exact Mem.Reads.write hwf hreads _ _

/-- **What `forwardArgTail` does**, both effects at once: it leaves argument
`k`'s declared tail length on the stack, writes that length into memory word
`lenWord`, and copies the payload into the word after it.

Every word named in the conclusion is a function of `e.data` alone
(`Sevm.tailLen`, `Sevm.tailBytes`), so this is a description of the fragment
rather than a restatement of its instructions — the discipline the arc's fixed
decision 2 requires of anything the callback's calldata image is built from.

No zero padding appears here: `forwardArgTail` writes the payload and nothing
above it, and a caller wanting a reference encoder's padding gets it from the
region above being untouched (see `forwardArgTail`'s own note and `Mem.Reads`). -/
lemma of_forwardArgTail_val {e : Sevm} {s s' : Devm} {k lenWord xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (forwardArgTail k lenWord) s') :
    (Sevm.tailLen e k :: xs <<+ s'.stack) ∧
      s'.memory =
        (s.memory.write (lenWord * 32).toNat (Sevm.tailLen e k).toBytes).write
          ((lenWord + 1) * 32).toNat (Sevm.tailBytes e k) := by
  -- The code computes `4 + off` while `Sevm.tailPtr` is written `off + 4`, and
  -- likewise `32 + p` against `Sevm.tailBytes`'s `tailPtr + 32`.  `B256` carries
  -- its own `HAdd`, so the commutations are `B256.add_comm`, not `add_comm`.
  have hptr : (4 : B256) + Sevm.argWord e k = Sevm.tailPtr e k := by
    rw [Sevm.tailPtr, B256.add_comm]
  have hoff : (32 : B256) + Sevm.tailPtr e k = Sevm.tailPtr e k + 32 := B256.add_comm
  simp only [forwardArgTail] at h
  -- `arg k`: the head word, which for a dynamic argument is an offset.
  rcases of_run_append (arg k) h with ⟨t1, q1, h⟩
  have hp1 : Sevm.argWord e k :: xs <<+ t1.stack := prefix_of_arg hp q1
  have hm1 : s.memory = t1.memory := Line.of_inv Devm.memory (by line_inv) q1
  -- `pushB256 4 :: add`: the absolute calldata index of the length word.
  rcases Line.of_run_cons h with ⟨t2, q2, h⟩
  have hb2 := of_run_pushB256 q2
  have hp2 : (4 : B256) :: Sevm.argWord e k :: xs <<+ t2.stack :=
    prefix_of_push hb2 hp1
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hp3 : Sevm.tailPtr e k :: xs <<+ t3.stack := by
    rw [← hptr]; exact prefix_of_add q3 hp2
  have hm3 : s.memory = t3.memory :=
    (hm1.trans hb2.memory).trans (Ninst.Hinv.inv (f := Devm.memory) q3)
  -- `dup 0 :: calldataload`: read the declared length, keeping the pointer.
  rcases Line.of_run_cons h with ⟨t4, q4, h⟩
  have hp4 : Sevm.tailPtr e k :: Sevm.tailPtr e k :: xs <<+ t4.stack :=
    prefix_of_dup_val q4 (Stack.Nth.head _ _) hp3
  have hm4 : s.memory = t4.memory := hm3.trans (Ninst.Hinv.inv (f := Devm.memory) q4)
  rcases Line.of_run_cons h with ⟨t5, q5, h⟩
  have hp5 : Sevm.tailLen e k :: Sevm.tailPtr e k :: xs <<+ t5.stack :=
    prefix_of_calldataload_val q5 hp4
  have hm5 : s.memory = t5.memory :=
    hm4.trans (Ninst.Hinv.inv (f := Devm.memory) q5)
  -- `dup 0 :: mstoreAt lenWord`: republish the length into memory.
  rcases Line.of_run_cons h with ⟨t6, q6, h⟩
  have hp6 : Sevm.tailLen e k :: Sevm.tailLen e k :: Sevm.tailPtr e k :: xs <<+ t6.stack :=
    prefix_of_dup_val q6 (Stack.Nth.head _ _) hp5
  have hm6 : s.memory = t6.memory := hm5.trans (Ninst.Hinv.inv (f := Devm.memory) q6)
  rcases of_run_append (mstoreAt lenWord) h with ⟨t7, q7, h⟩
  rcases of_run_mstoreAt_val q7 hp6 with ⟨hp7, hmw7⟩
  have hm7 : t7.memory =
      s.memory.write (lenWord * 32).toNat (Sevm.tailLen e k).toBytes := by
    rw [hmw7, hm6]
  -- `dup 0 :: swap 1`: the payload's source pointer back on top.
  rcases Line.of_run_cons h with ⟨t8, q8, h⟩
  have hp8 : Sevm.tailLen e k :: Sevm.tailLen e k :: Sevm.tailPtr e k :: xs <<+ t8.stack :=
    prefix_of_dup_val q8 (Stack.Nth.head _ _) hp7
  have hm8 := (Ninst.Hinv.inv (f := Devm.memory) q8).symm.trans hm7
  rcases Line.of_run_cons h with ⟨t9, q9, h⟩
  have hp9 : Sevm.tailPtr e k :: Sevm.tailLen e k :: Sevm.tailLen e k :: xs
      <<+ t9.stack := by
    have h_swap : Stack.Swap (1 : Fin 16).val
        (Sevm.tailLen e k :: Sevm.tailLen e k :: Sevm.tailPtr e k :: xs)
        (Sevm.tailPtr e k :: Sevm.tailLen e k :: Sevm.tailLen e k :: xs) := by
      apply Stack.swapCore_succ
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap (of_run_swap q9) hp8
  have hm9 := (Ninst.Hinv.inv (f := Devm.memory) q9).symm.trans hm8
  -- `pushB256 32 :: add`: the payload begins one word past the length word.
  rcases Line.of_run_cons h with ⟨t10, q10, h⟩
  have hb10 := of_run_pushB256 q10
  have hp10 : (32 : B256) :: Sevm.tailPtr e k :: Sevm.tailLen e k ::
      Sevm.tailLen e k :: xs <<+ t10.stack := prefix_of_push hb10 hp9
  have hm10 := hb10.memory.symm.trans hm9
  rcases Line.of_run_cons h with ⟨t11, q11, h⟩
  have hp11 : (32 + Sevm.tailPtr e k) :: Sevm.tailLen e k :: Sevm.tailLen e k ::
      xs <<+ t11.stack := prefix_of_add q11 hp10
  have hm11 := (Ninst.Hinv.inv (f := Devm.memory) q11).symm.trans hm10
  rcases Line.of_run_cons h with ⟨t12, q12, h⟩
  have hb12 := of_run_pushB256 q12
  have hp12 : ((lenWord + 1) * 32 : B256) :: (32 + Sevm.tailPtr e k) ::
      Sevm.tailLen e k :: Sevm.tailLen e k :: xs <<+ t12.stack :=
    prefix_of_push hb12 hp11
  have hm12 := hb12.memory.symm.trans hm11
  -- `calldatacopy`: the payload itself.
  rcases Line.of_run_cons h with ⟨t13, q13, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q13 hp12 with ⟨hps, hmem⟩
  refine ⟨hps, ?_⟩
  rw [hmem, hm12, Sevm.tailBytes, ← hoff]

/-! ### The returndata, value-carried

Arc B consumed `of_retdataShorterThan` / `of_checkRetdataHead` to learn that a
flag was pushed; the callback boundary (`~/plans/fmint-flashloan.md`, Step 4)
needs them to say what the returndata *is*.  The same projection-restoring
move as Step 1's calldata layer, applied to `RETURNDATASIZE`, `RETURNDATACOPY`
and `MLOAD`, then to the two `Line` fragments built from them. -/

/-- `RETURNDATASIZE` pushes the length of the last call's return data. -/
lemma of_run_retdatasize_val {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s retdatasize s') :
    Devm.PushBurn [s.returnData.length.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- `RETURNDATACOPY` writes *the returndata slice named by its operands* at
*the offset it popped* — and it got there without overrunning the returndata,
because an overrun is an exceptional halt, not a failed test (the reason
`retdataShorterThan` must be branched on first). -/
lemma of_run_retdatacopy_val {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s retdatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack ∧
      y.toNat + z.toNat ≤ s.returnData.length ∧
      s'.memory
        = s.memory.write x.toNat (s.returnData.sliceD y.toNat z.toNat 0) ∧
      s'.returnData = s.returnData := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  have hrd : s.returnData = s₄.returnData :=
    ((p1.returnData.trans p2.returnData).trans p3.returnData).trans hb.returnData
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  split at h5
  · cases h5
  · rename_i hbound
    injection h5 with eq
    refine ⟨x, y, z, ?_, ?_, ?_, ?_⟩
    · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
      rw [← eq, show (Devm.memWrite s₄ x.toNat _).stack = s₄.stack from rfl,
        ← hb.stack]
      exact hp
    · rw [hrd]
      omega
    · rw [← eq, hmem, hrd]
      rfl
    · rw [← eq, hrd]
      rfl

/-- `RETURNDATACOPY` at a *known* stack top. -/
lemma prefix_of_retdatacopy_val {e} {x y z xs} {s s' : Devm}
    (h0 : Ninst.Run e s retdatacopy s') (h1 : x :: y :: z :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧
      y.toNat + z.toNat ≤ s.returnData.length ∧
      s'.memory
        = s.memory.write x.toNat (s.returnData.sliceD y.toNat z.toNat 0) ∧
      s'.returnData = s.returnData := by
  rcases of_run_retdatacopy_val h0 with ⟨x', y', z', h2, hle, hm, hrd⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, hpf, hpf'⟩
  rcases List.of_cons_pref_of_cons_pref hpf hpf' with ⟨hz, -⟩
  rw [hx, hy, hz] at h1 ⊢
  exact ⟨of_append_pref h2 h1, hle, hm, hrd⟩

/-- The value a `Devm`-level memory read returns is the `Mem`-level one. -/
lemma Devm.memRead_fst (d : Devm) (i n : Nat) :
    (d.memRead i n).1 = (d.memory.read i n).1 := by
  unfold Devm.memRead
  rcases d.memory.read i n with ⟨val, mem⟩
  rfl

/-- Value-carrying inversion for `LOG`: besides the popped stack words, expose
the exact topics and the log entry appended from the pre-instruction memory.

The earlier `of_run_log` is intentionally the value-forgetting stack theorem;
this companion is the shared seam used by contract proofs that specify events
as part of their public behavior. -/
lemma of_run_log_val {e : Sevm} {s s' : Devm} {n : Fin 5}
    (h : Ninst.Run e s (log n) s') :
    ∃ mi sz topics,
      topics.length = n.val ∧
      Stack.Pop (mi :: sz :: topics) s.stack s'.stack ∧
      s'.logs =
        s.logs ++
          [⟨e.currentTarget, topics,
            (s.memory.read mi.toNat sz.toNat).1⟩] := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popN h3 with ⟨h_len, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases h_mem : Devm.memRead s₄ x.toNat y.toNat with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_pre_mem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  have h_data : data = (s.memory.read x.toNat y.toNat).1 := by
    have hd := congrArg Prod.fst h_mem
    simp only [Devm.memRead_fst] at hd
    rw [h_pre_mem]
    exact hd.symm
  have h_mem_logs : s₄.logs = s₅.logs := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read x.toNat y.toNat with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]
    rfl
  have h_pre_logs : s.logs = s₅.logs :=
    (((p1.logs.trans p2.logs).trans p3.logs).trans hb.logs).trans h_mem_logs
  refine ⟨x, y, topics, h_len, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq]
    show Stack.Pop (x :: y :: topics) s.stack s₅.stack
    have h_s₅_stack : s₅.stack = s₄.stack := by
      simp only [Devm.memRead] at h_mem
      rcases h_read : s₄.memory.read x.toNat y.toNat with ⟨val, mem⟩
      rw [h_read] at h_mem
      injection h_mem with _ h_devm
      rw [← h_devm]
      rfl
    rw [h_s₅_stack, ← hb.stack]
    exact hp
  · rw [← eq]
    show s₅.logs ++ [⟨e.currentTarget, topics, data⟩] =
      s.logs ++
        [⟨e.currentTarget, topics, (s.memory.read x.toNat y.toNat).1⟩]
    rw [← h_pre_logs, h_data]

/-- Exact stack and log effect of any fixed-shape `logWith` fragment.

The topic list includes the signature topic, hence its length is `k + 1`.
This general form covers data-less one- and two-topic control-plane events as
well as multiword unindexed data windows; specialized ERC-20 helpers remain
available below. -/
lemma of_logWith_val {e : Sevm} {s s' : Devm} {k : Fin 4}
    {x y : B256} {topics : List B256} {xs : Stack}
    (hlen : topics.length = k.val + 1)
    (hp : topics ++ xs <<+ s.stack)
    (h : Line.Run e s (logWith k x y) s') :
    xs <<+ s'.stack ∧
      s'.logs = s.logs ++
        [⟨e.currentTarget, topics,
          (s.memory.read (x * 32).toNat (y * 32).toNat).1⟩] := by
  rcases Line.of_run_cons h with ⟨s₁, hsize, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, hoffset, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hbsize := of_run_pushB256 hsize
  have hboffset := of_run_pushB256 hoffset
  have hp₁ : (y * 32) :: topics ++ xs <<+ s₁.stack :=
    prefix_of_push (xs := [y * 32]) (ys := topics ++ xs) hbsize hp
  have hp₂ : (x * 32) :: (y * 32) :: topics ++ xs <<+ s₂.stack :=
    prefix_of_push (xs := [x * 32])
      (ys := (y * 32) :: topics ++ xs) hboffset hp₁
  rcases of_run_log_val hlog with
    ⟨mi, sz, actualTopics, hactualLen, hpop, hlogs⟩
  have hknown : ((x * 32) :: (y * 32) :: topics) <<+ s₂.stack := by
    exact @pref_trans _ ((x * 32) :: (y * 32) :: topics)
      (((x * 32) :: (y * 32) :: topics) ++ xs) _
      ⟨xs, rfl⟩ (by simpa [List.append_assoc] using hp₂)
  have heq : ((x * 32) :: (y * 32) :: topics) =
      mi :: sz :: actualTopics :=
    List.pref_unique (by simp [hlen, hactualLen]) hknown
      (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  constructor
  · exact of_append_pref hpop (by simpa [List.append_assoc] using hp₂)
  · rw [hlogs, ← hboffset.logs, ← hbsize.logs,
      ← hboffset.memory, ← hbsize.memory]

/-- A fixed-shape `logWith` preserves any proof-carrying memory image and its
well-formedness; its only memory effect is the read-window extension performed
by `LOG`. -/
lemma of_logWith_image {e : Sevm} {s s' : Devm} {k : Fin 4}
    {x y : B256} {image : Bytes}
    (hwf : Mem.Wf s.memory) (hreads : Mem.Reads s.memory image)
    (h : Line.Run e s (logWith k x y) s') :
    Mem.Wf s'.memory ∧ Mem.Reads s'.memory image := by
  rcases Line.of_run_cons h with ⟨s₁, hsize, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, hoffset, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨_, hlog, hnil⟩
  cases hnil
  have hbsize := of_run_pushB256 hsize
  have hboffset := of_run_pushB256 hoffset
  obtain ⟨mi, sz, hmemory⟩ := of_run_log_mem hlog
  constructor
  · rw [hmemory, ← hboffset.memory, ← hbsize.memory]
    exact hwf.extend mi sz
  · rw [hmemory, ← hboffset.memory, ← hbsize.memory]
    exact hreads.extend mi sz

/-- Exact event effect of the canonical three-topic, one-word log fragment.

`logWith 2 0 1` is the common shape of ERC-20 `Transfer` and `Approval`:
topic0 plus two indexed addresses, and one ABI word read from memory `[0, 32)`.
The theorem keeps the existing stack-prefix API while making the appended log
available to public functional proofs. -/
lemma of_logWith201_val {e : Sevm} {s s' : Devm}
    {ev a b : B256} {xs : Stack}
    (hp : ev :: a :: b :: xs <<+ s.stack)
    (h : Line.Run e s (logWith 2 0 1) s') :
    xs <<+ s'.stack ∧
      s'.logs =
        s.logs ++ [⟨e.currentTarget, [ev, a, b], (s.memory.read 0 32).1⟩] := by
  rcases Line.of_run_cons h with ⟨s₁, h32, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, h0, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hb32 := of_run_pushB256 h32
  have hb0 := of_run_pushB256 h0
  have h32word : (1 * 32 : B256) = 32 := by decide +kernel
  have h0word : (0 * 32 : B256) = 0 := by decide +kernel
  rw [h32word] at hb32
  rw [h0word] at hb0
  have hp₁ : (32 : B256) :: ev :: a :: b :: xs <<+ s₁.stack := by
    simpa using prefix_of_push hb32 hp
  have hp₂ : (0 : B256) :: 32 :: ev :: a :: b :: xs <<+ s₂.stack := by
    simpa using prefix_of_push hb0 hp₁
  rcases of_run_log_val hlog with
    ⟨mi, sz, topics, hlen, hpop, hlogs⟩
  have hknown : ([0, 32, ev, a, b] : List B256) <<+ s₂.stack := by
    exact @pref_trans _ [0, 32, ev, a, b]
      ([0, 32, ev, a, b] ++ xs) _ ⟨xs, rfl⟩ (by simpa using hp₂)
  have heq : ([0, 32, ev, a, b] : List B256) = mi :: sz :: topics :=
    List.pref_unique (by simp [hlen]) hknown (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  constructor
  · exact of_append_pref hpop (by simpa using hp₂)
  · rw [hlogs, ← hb0.logs, ← hb32.logs, ← hb0.memory, ← hb32.memory]
    rfl

/-- Exact memory-extension companion for `of_logWith201_val`.

The two setup pushes preserve memory, while `LOG3` reads the single ABI word
at `[0, 32)` and therefore leaves precisely the memory extension performed by
that read.  This is kept separate from the event theorem so existing consumers
of its stable stack/log interface are unaffected. -/
lemma of_logWith201_mem {e : Sevm} {s s' : Devm}
    {ev a b : B256} {xs : Stack}
    (hp : ev :: a :: b :: xs <<+ s.stack)
    (h : Line.Run e s (logWith 2 0 1) s') :
    s'.memory = s.memory.extend 0 32 := by
  rcases Line.of_run_cons h with ⟨s₁, h32, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, h0, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hb32 := of_run_pushB256 h32
  have hb0 := of_run_pushB256 h0
  have h32word : (1 * 32 : B256) = 32 := by decide +kernel
  have h0word : (0 * 32 : B256) = 0 := by decide +kernel
  rw [h32word] at hb32
  rw [h0word] at hb0
  have hp₁ : (32 : B256) :: ev :: a :: b :: xs <<+ s₁.stack := by
    simpa using prefix_of_push hb32 hp
  have hp₂ : (0 : B256) :: 32 :: ev :: a :: b :: xs <<+ s₂.stack := by
    simpa using prefix_of_push hb0 hp₁
  rcases of_run_log_mem_val hlog with
    ⟨mi, sz, topics, hlen, hpop, hmemory⟩
  have hknown : ([0, 32, ev, a, b] : List B256) <<+ s₂.stack := by
    exact @pref_trans _ [0, 32, ev, a, b]
      ([0, 32, ev, a, b] ++ xs) _ ⟨xs, rfl⟩ (by simpa using hp₂)
  have heq : ([0, 32, ev, a, b] : List B256) = mi :: sz :: topics :=
    List.pref_unique (by simp [hlen]) hknown (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  rw [hmemory, ← hb0.memory, ← hb32.memory]
  rfl

/-- `MLOAD` pushes *the word at the offset it popped*, and only extends
memory.  The value-carrying companion of `of_run_mload`. -/
lemma of_run_mload_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mload s') :
    ∃ x, Stack.Diff [x] [Bytes.toB256 (s.memory.read x.toNat 32).1]
        s.stack s'.stack ∧
      s'.memory = s.memory.extend x.toNat 32 ∧
      s'.returnData = s.returnData := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have hb := Devm.burn_of_chargeGas h2
  have hpush := Devm.push_of_push run₂
  have hmem : s.memory = s₂.memory := p1.memory.trans hb.memory
  have hrd : s.returnData = s₂.returnData := p1.returnData.trans hb.returnData
  refine ⟨x, ⟨s₁.stack, p1.stack, ?_⟩, ?_, ?_⟩
  · have hstk := hpush.stack
    rw [show (s₂.memRead x.toNat 32).2.stack = s₂.stack from rfl,
      ← hb.stack] at hstk
    rw [show (s₂.memRead x.toNat 32).1 = (s.memory.read x.toNat 32).1 from by
      rw [Devm.memRead_fst, hmem]] at hstk
    exact hstk
  · have hm := hpush.memory
    rw [show (s₂.memRead x.toNat 32).2.memory = s₂.memory.extend x.toNat 32 from
      rfl] at hm
    rw [← hm, ← hmem]
  · rw [← hpush.returnData]
    show s₂.returnData = s.returnData
    exact hrd.symm

/-- `MLOAD` at a *known* stack top against a known memory image: the pushed
word is the image's word at that offset, and the image survives the
extension. -/
lemma prefix_of_mload_val {e} {x : B256} {xs bs} {s s' : Devm}
    (h0 : Ninst.Run e s mload s') (h1 : x :: xs <<+ s.stack)
    (hr : Mem.Reads s.memory bs) :
    (Bytes.toB256 (bs.sliceD x.toNat 32 0) :: xs <<+ s'.stack) ∧
      s'.memory = s.memory.extend x.toNat 32 ∧
      s'.returnData = s.returnData := by
  rcases of_run_mload_val h0 with ⟨x', ⟨stk, h2, h3⟩, hm, hrd⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  rw [Mem.Reads.read hr x.toNat 32] at h3
  exact ⟨append_pref h3 (of_append_pref h2 h1), hm, hrd⟩

/-- Load one fixed scratch word against a proof-carrying memory image.  The
caller supplies the image equation for that word; the line preserves the image
and state while pushing the named value. -/
theorem of_run_loadWordAt_image
    {e : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hvalue : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run e pre [pushB256 (word * 32), mload] post) :
    value :: tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory image ∧
      pre.state = post.state := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have pPush := prefix_of_push pushed hp
  have pushWf : Mem.Wf afterPush.memory := by
    rw [← pushed.memory]
    exact hwf
  have pushReads : Mem.Reads afterPush.memory image := by
    rw [← pushed.memory]
    exact hreads
  obtain ⟨loaded, memory, _⟩ :=
    prefix_of_mload_val loadRun pPush pushReads
  refine ⟨?_, ?_, ?_, Line.of_inv Devm.state (by line_inv)
    (Line.Run.cons pushRun (Line.Run.cons loadRun Line.Run.nil))⟩
  · simpa [hvalue] using loaded
  · rw [memory]
    exact pushWf.extend _ _
  · rw [memory]
    exact pushReads.extend _ _

/-- `of_run_loadWordAt_image` with the exact memory extension retained.  This
is useful when the caller can prove the read window was already covered and
therefore collapse the extension back to the original memory. -/
theorem of_run_loadWordAt_image_memory
    {e : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hvalue : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run e pre [pushB256 (word * 32), mload] post) :
    value :: tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory image ∧
      pre.state = post.state ∧
      post.memory = pre.memory.extend (word * 32).toNat 32 := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have pPush := prefix_of_push pushed hp
  have pushWf : Mem.Wf afterPush.memory := by
    rw [← pushed.memory]
    exact hwf
  have pushReads : Mem.Reads afterPush.memory image := by
    rw [← pushed.memory]
    exact hreads
  obtain ⟨loaded, memory, _⟩ :=
    prefix_of_mload_val loadRun pPush pushReads
  refine ⟨?_, ?_, ?_, Line.of_inv Devm.state (by line_inv)
    (Line.Run.cons pushRun (Line.Run.cons loadRun Line.Run.nil)), ?_⟩
  · simpa [hvalue] using loaded
  · rw [memory]
    exact pushWf.extend _ _
  · rw [memory]
    exact pushReads.extend _ _
  · rw [memory, ← pushed.memory]

/-- A fixed scratch-word load is log-silent.  `MLOAD` has no global
`Ninst.Hinv` instance for logs, so expose the exact two-instruction fact at
the shared line altitude instead of reproving its register walk in every
constructor or decoder. -/
theorem of_run_loadWordAt_logs
    {e : Sevm} {pre post : Devm} {word : B256}
    (run : Line.Run e pre [pushB256 (word * 32), mload] post) :
    pre.logs = post.logs := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  rcases of_run_reg loadRun with ⟨_, regRun⟩
  simp only [Rinst.run, Rinst.runCore] at regRun
  rcases Except.bind_eq_ok regRun with ⟨⟨_, popPost⟩, popRun, regRun⟩
  rcases Except.bind_eq_ok regRun with ⟨burnPost, burnRun, pushResult⟩
  rcases Devm.pop_of_popToNat popRun with ⟨_, popped⟩
  have burned := Devm.burn_of_chargeGas burnRun
  have pushed := Devm.push_of_push pushResult
  exact (of_run_pushB256 pushRun).logs.trans
    (((popped.logs.trans burned.logs).trans rfl).trans pushed.logs)

/-- `retdataShorterThan n`, with its flag: the fragment pushes exactly the
comparison `retdatasize <? n` and touches nothing else. -/
lemma of_retdataShorterThan_val {e : Sevm} {s s' : Devm} {n : B256} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (retdataShorterThan n) s') :
    ((s.returnData.length.toB256 <? n) :: xs <<+ s'.stack) ∧
      s'.memory = s.memory ∧ s'.returnData = s.returnData := by
  simp only [retdataShorterThan] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : n :: xs <<+ u1.stack := prefix_of_push hb1 hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_retdatasize_val q2
  rw [← hb1.returnData] at hb2
  have hp2 : s.returnData.length.toB256 :: n :: xs <<+ u2.stack :=
    prefix_of_push hb2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ : ∃ a b, Devm.DiffBurn [a, b] [B256.ltCheck a b] u2 s' := by
    rcases of_run_reg q3 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  refine ⟨prefix_of_lt q3 hp2, ?_, ?_⟩
  · rw [← hdb.memory, ← hb2.memory, ← hb1.memory]
  · rw [← hdb.returnData, ← hb2.returnData, ← hb1.returnData]

/-- `checkRetdataHead w m`, with its flag: the word the fragment compares
against `w` is *the returndata's head word*, read back through the memory word
it clobbers.  Carries the non-overrun bound the copy enforces — returndata of
at least a word, the reason `retdataShorterThan` is branched on first — and
the memory image after the clobber. -/
lemma of_checkRetdataHead_val {e : Sevm} {s s' : Devm} {w m : B256} {bs : Bytes}
    {xs}
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory bs)
    (h : Line.Run e s (checkRetdataHead w m) s') :
    ((w =? Bytes.toB256 (s.returnData.sliceD 0 32 0)) :: xs <<+ s'.stack) ∧
      32 ≤ s.returnData.length ∧
      Mem.Wf s'.memory ∧
      Mem.Reads s'.memory
        (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) ∧
      s'.returnData = s.returnData := by
  simp only [checkRetdataHead, pushList, List.map] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : (32 : B256) :: xs <<+ u1.stack := prefix_of_push hb1 hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_pushB256 q2
  have hp2 : (0 : B256) :: (32 : B256) :: xs <<+ u2.stack :=
    prefix_of_push hb2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hb3 := of_run_pushB256 q3
  have hp3 : (m * 32) :: (0 : B256) :: (32 : B256) :: xs <<+ u3.stack :=
    prefix_of_push hb3 hp2
  have hm3 : s.memory = u3.memory := (hb1.memory.trans hb2.memory).trans hb3.memory
  have hrd3 : s.returnData = u3.returnData :=
    (hb1.returnData.trans hb2.returnData).trans hb3.returnData
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  rcases prefix_of_retdatacopy_val q4 hp3 with ⟨hp4, hle4, hm4, hrd4⟩
  have hle : 32 ≤ s.returnData.length := by
    rw [hrd3]
    rw [show ((0 : B256)).toNat = 0 from rfl,
      show ((32 : B256)).toNat = 32 from rfl] at hle4
    omega
  have hslice : u3.returnData.sliceD ((0 : B256)).toNat ((32 : B256)).toNat 0
      = s.returnData.sliceD 0 32 0 := by
    rw [← hrd3, show ((0 : B256)).toNat = 0 from rfl,
      show ((32 : B256)).toNat = 32 from rfl]
  have hwf4 : Mem.Wf u4.memory := by
    rw [hm4, ← hm3]
    exact hwf.write _ _
  have hr4 : Mem.Reads u4.memory
      (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) := by
    rw [hm4, ← hm3, hslice]
    exact hr.write hwf _ _
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hb5 := of_run_pushB256 q5
  have hp5 : (m * 32) :: xs <<+ u5.stack := prefix_of_push hb5 hp4
  have hwf5 : Mem.Wf u5.memory := by
    rw [← hb5.memory]
    exact hwf4
  have hr5 : Mem.Reads u5.memory
      (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) := by
    rw [← hb5.memory]
    exact hr4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  rcases prefix_of_mload_val q6 hp5 hr5 with ⟨hp6, hm6, hrd6⟩
  have hlen32 : (s.returnData.sliceD 0 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  have hhead : (Bytes.writeAt bs (m * 32).toNat
      (s.returnData.sliceD 0 32 0)).sliceD ((m * 32)).toNat 32 0
      = s.returnData.sliceD 0 32 0 := by
    conv_lhs =>
      rw [show (32 : Nat) = (s.returnData.sliceD 0 32 0).length from
        hlen32.symm]
    exact Bytes.sliceD_writeAt bs _ _
  rw [hhead] at hp6
  have hwf6 : Mem.Wf u6.memory := by
    rw [hm6]
    exact hwf5.extend _ _
  have hr6 : Mem.Reads u6.memory
      (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) := by
    rw [hm6]
    exact hr5.extend _ _
  rcases Line.of_run_cons h with ⟨u7, q7, h⟩
  have hb7 := of_run_pushB256 q7
  have hp7 : w :: Bytes.toB256 (s.returnData.sliceD 0 32 0) :: xs <<+ u7.stack :=
    prefix_of_push hb7 hp6
  rcases Line.of_run_cons h with ⟨u8, q8, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ : ∃ a b, Devm.DiffBurn [a, b] [B256.eqCheck a b] u7 s' := by
    rcases of_run_reg q8 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  refine ⟨prefix_of_eq q8 hp7, hle, ?_, ?_, ?_⟩
  · rw [← hdb.memory, ← hb7.memory]
    exact hwf6
  · rw [← hdb.memory, ← hb7.memory]
    exact hr6
  · rw [← hdb.returnData, ← hb7.returnData, hrd6, ← hb5.returnData, hrd4,
      ← hrd3]

/-! ### The dynamic tail of a canonically encoded call

`forwardArgTail 3` follows argument 3's head word to its length word and copies
the payload from there.  Under `Sevm.DecodesCallWithTail` those reads recover
exactly the `data` the encoding was built from — the round-trip that keeps a
statement about the forwarded bytes a statement about `data` rather than about
whatever the contract happens to read, which is the vacuity the arc's fixed
decision 2 forbids.

The length premise is unavoidable rather than convenient: `List.length` is an
unbounded `Nat` while the ABI's length word is 256 bits, so `data` longer than
`2 ^ 256` bytes would not round-trip through the encoding at all. -/

lemma tailPtr_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.tailPtr e 3 = Nat.toB256 132 := by
  simp only [Sevm.tailPtr, argWord_three_of_decodes h]
  rfl

/-- The encoding, split at the tail's length word. -/
lemma decodes_split_tail {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    e.data = (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
      B256.toBytes c ++ B256.toBytes (Nat.toB256 128)) ++
      (B256.toBytes (Nat.toB256 data.length) ++
        (data ++ List.replicate (ceil32 data.length - data.length) 0)) := by
  simpa [Sevm.DecodesCallWithTail, abiCallWithTail, abiBytesTail,
    List.append_assoc] using h

lemma decodes_head_length (sel a b c : B256) :
    (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
      B256.toBytes c ++ B256.toBytes (Nat.toB256 128)).length = 132 := by
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
    abiSelectorBytes_length, B256.length_toBytes, B256.length_toBytes,
    B256.length_toBytes, B256.length_toBytes]

lemma tailLen_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.tailLen e 3 = Nat.toB256 data.length := by
  rw [Sevm.tailLen, tailPtr_three_of_decodes h]
  exact dataWord_of_append (by rw [decodes_head_length]; rfl) (decodes_split_tail h)

lemma tailBytes_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (hlen : data.length < 2 ^ 256)
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.tailBytes e 3 = data := by
  have hnat : (Nat.toB256 data.length).toNat = data.length := by
    rw [B256.toNat_toB256]
    exact Nat.mod_eq_of_lt hlen
  simp only [Sevm.tailBytes, tailPtr_three_of_decodes h, tailLen_three_of_decodes h,
    hnat]
  have hd : e.data =
      ((abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
        B256.toBytes c ++ B256.toBytes (Nat.toB256 128)) ++
        B256.toBytes (Nat.toB256 data.length)) ++
      (data ++ List.replicate (ceil32 data.length - data.length) 0) := by
    rw [List.append_assoc]; exact decodes_split_tail h
  have hpre : ((abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
      B256.toBytes c ++ B256.toBytes (Nat.toB256 128)) ++
      B256.toBytes (Nat.toB256 data.length)).length = 164 := by
    rw [List.length_append, decodes_head_length, B256.length_toBytes]
  show List.sliceD e.data (Nat.toB256 132 + 32).toNat data.length 0 = data
  rw [show (Nat.toB256 132 + (32 : B256)).toNat = 164 from rfl, hd,
    List.sliceD, List.drop_length_append' (by rw [hpre]),
    List.takeD_eq_take _ (by simp [List.length_append]),
    List.take_length_append' rfl]

/-! ### `ceil32` as the EVM computes it

Every Solidity-shaped contract rounds a byte length up to a whole word with
`(len + 31) & ~31`, and a statement about the resulting `argsSize` is a
statement about `ceil32` only once that identity is proved.  `B256` is a nested
pair of `UInt64`s rather than a `BitVec`, so none of the usual bitvector API
applies and there was no `toNat` lemma for `&&&` at all; the three lemmas below
build one, and `bv_decide` is barred here (the protected cone's ban, and 256
bits would be infeasible regardless).

The bound `31 + len < 2 ^ 256` is the same kind of premise as
`tailBytes_three_of_decodes`'s: `List.length` is an unbounded `Nat` while the
machine word is 256 bits. -/

/-- Bitwise `and` distributes over a shift-and-or split of both sides, provided
the low halves fit below the shift.  The one bit-level fact the `B128`/`B256`
`toNat` homomorphisms need. -/
lemma Nat.and_or_shiftLeft {a b c d k : Nat} (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    ((a <<< k ||| b) &&& (c <<< k ||| d)) = ((a &&& c) <<< k) ||| (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
  by_cases hi : k ≤ i
  · have hpow : (2 : Nat) ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd hpow)]
    simp [hi]
  · simp [hi]

lemma B128.toNat_and (x y : B128) : (x &&& y).toNat = x.toNat &&& y.toNat := by
  show ((x.1 &&& y.1).toNat <<< 64) ||| (x.2 &&& y.2).toNat = _
  rw [UInt64.toNat_and, UInt64.toNat_and]
  exact (Nat.and_or_shiftLeft (UInt64.toNat_lt x.2) (UInt64.toNat_lt y.2)).symm

lemma B256.toNat_and (x y : B256) : (x &&& y).toNat = x.toNat &&& y.toNat := by
  show ((x.1 &&& y.1).toNat <<< 128) ||| (x.2 &&& y.2).toNat = _
  rw [B128.toNat_and, B128.toNat_and]
  exact (Nat.and_or_shiftLeft (B128.toNat_lt (x := x.2)) (B128.toNat_lt (x := y.2))).symm

/-- Masking off the low five bits is division by `32`.  `2 ^ 256 - 32` is
`(2 ^ 251 - 1) <<< 5`, so both sides agree bit by bit. -/
lemma Nat.and_mask32 {n : Nat} (h : n < 2 ^ 256) :
    n &&& (2 ^ 256 - 32) = 32 * (n / 32) := by
  have hm : (2 : Nat) ^ 256 - 32 = (2 ^ 251 - 1) <<< 5 := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add]
  have hr : 32 * (n / 32) = (n >>> 5) <<< 5 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  rw [hm, hr]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : 5 ≤ i
  · rw [show 5 + (i - 5) = i from by omega]
    simp only [ge_iff_le, hi, decide_true, Bool.true_and]
    by_cases hi2 : i < 256
    · rw [decide_eq_true (by omega : i - 5 < 251), Bool.and_true]
    · rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))]
      rw [Bool.false_and]
  · simp only [ge_iff_le, hi, decide_false, Bool.false_and, Bool.and_false]

lemma ceil32_eq_mul (len : Nat) : ceil32 len = 32 * ((31 + len) / 32) := by
  unfold ceil32
  rcases hm : len % 32 with _ | m
  · show len = _; omega
  · show len + 32 - (m + 1) = _; omega

/-- **`(len + 31) & ~31` is `ceil32 len`**, as a `Nat`. -/
lemma B256.toNat_ceil32 {len : Nat} (h : 31 + len < 2 ^ 256) :
    ((~~~ (31 : B256)) &&& (31 + Nat.toB256 len)).toNat = ceil32 len := by
  have hy : ((31 : B256) + Nat.toB256 len).toNat = 31 + len := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega : len < 2 ^ 256),
      show B256.toNat 31 = 31 from rfl, Nat.lo_eq_of_lt h]
  rw [B256.toNat_and, show (~~~ (31 : B256)).toNat = 2 ^ 256 - 32 from rfl,
    Nat.and_comm, hy, Nat.and_mask32 h, ceil32_eq_mul]

/-! ### The weak form of a partial-correctness theorem: settles with some error

`exec` is Jaune's total function into `Execution := Except (EvmError × Devm)
Devm`, so it is defined on every `Evm`.  A statement of the form "no `.ok`
outcome exists" therefore already implies the positive claim "this call
settles with *some* error" — the case `exec` did not take is the only one
left.  This is `~/plans/error-genre.md`'s E-A: the generic bridge, contract-
agnostic and mentioning no `Func`, `Prog`, or contract of Blanc's. -/

/-- **A frame with no successful outcome settles with some error.**  Cases on
the total function's result: the `.ok` branch is excluded by `h` via
`exec_iff_exec_eq`, which turns the excluded `Exec … (.ok post)` derivation
into the excluded `exec` equation; the `.error` branch is the conclusion
itself. Names no error kind — only that `exec` did not return `.ok`. -/
lemma exec_error_of_no_success {sevm : Sevm} {pre : Devm}
    (h : ∀ post, Exec 0 sevm pre (.ok post) → False) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) := by
  rcases hexec : exec ⟨0, sevm, pre⟩ with ⟨e, post⟩ | post
  · exact ⟨e, post, rfl⟩
  · exact absurd ((exec_iff_exec_eq 0 sevm pre (.ok post)).mpr hexec)
      (fun ⟨a⟩ => h post a)

end Blanc
