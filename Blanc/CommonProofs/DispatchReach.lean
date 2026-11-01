-- CommonProofs/DispatchReach.lean : dispatcher reachability and dispatch log frames.

import Blanc.CommonProofs.Hinv

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

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
  rw [show (sig =? sig) = 1 from by simp only [B256.eqCheck, ↓reduceIte]] at h_pfx1
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
          rw [B256.gtCheck, ite_eq_left h_gt] at h_flag
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
          rw [B256.gtCheck, ite_eq_right (fun h_gt => h_nlt h_gt)] at h_flag
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

/-! ### Inline-revert dispatch reachability

`dispatch` has the same balanced-search shape as `dispatchWith`, but a leaf
miss executes `Func.revert` directly instead of tail-calling a fallback slot.
The successful selected-body theorem is therefore strictly simpler at the
leaf while retaining the same sortedness and frame guarantees. -/

private lemma reach_of_dispatch_leaf {sig w : B256} {f p : Func}
    {c : List Func} {e : Sevm} {s r : Devm} {ws : Stack}
    (h_mem : (sig, f) ∈ [(w, p)])
    (h_pfx : sig :: ws <<+ s.stack) :
    Func.Run c e s (dispatch (DispatchTree.leaf w p)) r →
    ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      Func.Run c e s' f r := by
  have h_eq : (sig, f) = (w, p) := List.mem_singleton.mp h_mem
  injection h_eq with h_sig h_f
  subst h_sig
  subst h_f
  func_execute 2
  intro h₂
  have h_pfx1 : (sig =? sig) :: ws <<+ s₁.stack := by
    generalize_line_prefix
  rw [show (sig =? sig) = 1 from by simp only [B256.eqCheck, ↓reduceIte]] at h_pfx1
  rcases of_run_branch h₂ with
      ⟨s₂, h_pop, h_runf⟩ |
      ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_runf⟩
  · exact absurd h_runf not_run_revert
  · rcases popBurn_pref h_pop h_pfx1 with ⟨-, h_pfx2⟩
    refine ⟨s₃, ?_, ?_, ?_, h_runf⟩
    · rw [← h_burn.stack]
      exact h_pfx2
    · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
        (h_pop.state.trans h_burn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
        (h_pop.memory.trans h_burn.memory)

private theorem reach_of_dispatch_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {c : List Func} {e : Sevm} {s r : Devm} {ws : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (sig :: ws <<+ s.stack) →
      Func.Run c e s (dispatch (DispatchTree.build n xs)) r →
      ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
        Func.Run c e s' f r := by
  intro n
  induction n with
  | zero =>
    intro xs sig f c e s r ws h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatch_leaf h_mem h_pfx
    · intro _
      exfalso
      simp only [List.length_cons] at h_len
      omega
  | succ n ih =>
    intro xs sig f c e s r ws h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatch_leaf h_mem h_pfx
    ·
      simp only [List.length_cons] at h_len
      have h_take_len :
          (((w, p) :: y :: ys).take
            ((((w, p) :: y :: ys).length + 1) / 2)).length ≤ n + 1 := by
        simp only [List.length_take, List.length_cons]
        omega
      have h_drop_len :
          (((w, p) :: y :: ys).drop
            ((((w, p) :: y :: ys).length + 1) / 2)).length ≤ n + 1 := by
        simp only [List.length_drop, List.length_cons]
        omega
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
        rw [List.take_append_drop]
        exact h_sorted
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
      func_execute 3
      intro h₂
      have h_pfx1 :
          (leftmostFsig (DispatchTree.build n
            (((w, p) :: y :: ys).drop
              ((((w, p) :: y :: ys).length + 1) / 2))) >? sig) ::
            sig :: ws <<+ s₁.stack := by
        generalize_line_prefix
      rw [h_drop, DispatchTree.leftmostFsig_build] at h_pfx1
      rcases of_run_branch h₂ with
          ⟨s₂, h_pop, h_run'⟩ |
          ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_run'⟩
      ·
        rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
        have h_le : z.fst ≤ sig := by
          rw [← B256.not_lt]
          intro h_lt
          have h_gt : z.fst > sig := h_lt
          rw [B256.gtCheck, ite_eq_left h_gt] at h_flag
          exact B256.zero_ne_one h_flag
        have h_mem_drop : (sig, f) ∈
            ((w, p) :: y :: ys).drop
              ((((w, p) :: y :: ys).length + 1) / 2) := by
          rcases h_mem_split with h_in | h_in
          · exfalso
            have h_z : z ∈ ((w, p) :: y :: ys).drop
                ((((w, p) :: y :: ys).length + 1) / 2) := by
              rw [h_drop]
              exact List.mem_cons_self ..
            have h_lt := DispatchTree.fst_lt_of_sorted_append
              h_sorted_split h_in h_z
            have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
            have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
            omega
          · exact h_in
        rcases ih h_sorted_drop h_drop_len h_mem_drop h_pfx2 h_run'
          with ⟨s', h_s', h_st, h_mm, h_rf⟩
        refine ⟨s', h_s', ?_, ?_, h_rf⟩
        · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
            (h_pop.state.trans h_st)
        · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
            (h_pop.memory.trans h_mm)
      ·
        rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
        have h_lt : sig < z.fst := by
          by_contra h_nlt
          rw [B256.gtCheck, ite_eq_right (fun h_gt => h_nlt h_gt)] at h_flag
          exact h_ne h_flag
        have h_mem_take : (sig, f) ∈
            ((w, p) :: y :: ys).take
              ((((w, p) :: y :: ys).length + 1) / 2) := by
          rcases h_mem_split with h_in | h_in
          · exact h_in
          · exfalso
            rw [h_drop] at h_in
            have h_sorted_zzs : DispatchTree.sorted (z :: zs) = true := by
              rw [← h_drop]
              exact h_sorted_drop
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

/-- **Inline-revert dispatch reachability.** A successful run over a sorted
function list factors through the entry paired with the selector on top of the
stack. The selector is removed and the dispatcher preserves world state and
memory; selector misses cannot produce a successful run. -/
theorem reach_of_dispatch {funcs : List (B256 × Func)}
    {sig : B256} {f : Func} {c : List Func} {e : Sevm} {s r : Devm}
    {ws : Stack}
    (h_sorted : DispatchTree.sorted funcs = true)
    (h_mem : (sig, f) ∈ funcs)
    (h_pfx : sig :: ws <<+ s.stack)
    (h_run : Func.Run c e s (dispatch (DispatchTree.ofSorted funcs)) r) :
    ∃ s', (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      Func.Run c e s' f r :=
  reach_of_dispatch_build h_sorted (Nat.le_succ _) h_mem h_pfx h_run

/-- **Inline-revert dispatch misses cannot succeed.** `Func.Run` is the
successful source relation, so a selector with no leaf in the tree has no
successful dispatcher run at all: every branch it can take ends at the inline
`Func.revert`.  This is the source-level counterpart of
`DispatchTree.dispatchMiss_runCompiledTo_with_path`, and it is what turns a
contract's selector census into "every successful call is one of these
entries". -/
theorem not_run_dispatch_of_miss :
    ∀ {tree : DispatchTree} {sig : B256} {c : List Func} {e : Sevm}
      {s r : Devm} {ws : Stack},
      (∀ body : Func, (sig, body) ∉ tree) →
      (sig :: ws <<+ s.stack) →
      Func.Run c e s (dispatch tree) r → False := by
  intro tree
  induction tree with
  | leaf w p =>
    intro sig c e s r ws h_miss h_pfx
    have h_ne : w ≠ sig := by
      intro h_eq
      exact h_miss p (show (sig, p) = (w, p) by rw [h_eq])
    func_execute 2
    intro h₂
    have h_pfx1 : (w =? sig) :: ws <<+ s₁.stack := by
      generalize_line_prefix
    rw [B256.eqCheck, ite_eq_right h_ne] at h_pfx1
    rcases of_run_branch h₂ with
        ⟨s₂, h_pop, h_runf⟩ |
        ⟨v, s₂, s₃, h_vne, h_pop, h_burn, h_runf⟩
    · exact not_run_revert h_runf
    · rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, -⟩
      exact h_vne h_flag
  | fork tl tr ihl ihr =>
    intro sig c e s r ws h_miss h_pfx
    have h_missl : ∀ body : Func, (sig, body) ∉ tl := by
      intro body h_mem
      exact h_miss body (Or.inl h_mem)
    have h_missr : ∀ body : Func, (sig, body) ∉ tr := by
      intro body h_mem
      exact h_miss body (Or.inr h_mem)
    func_execute 3
    intro h₂
    have h_pfx1 : (leftmostFsig tr >? sig) :: sig :: ws <<+ s₁.stack := by
      generalize_line_prefix
    rcases of_run_branch h₂ with
        ⟨s₂, h_pop, h_run'⟩ |
        ⟨v, s₂, s₃, h_vne, h_pop, h_burn, h_run'⟩
    · rcases popBurn_pref h_pop h_pfx1 with ⟨-, h_pfx2⟩
      exact ihr h_missr h_pfx2 h_run'
    · rcases popBurn_pref h_pop h_pfx1 with ⟨-, h_pfx2⟩
      rw [h_burn.stack] at h_pfx2
      exact ihl h_missl h_pfx2 h_run'

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
  have hshr : s3.logs = t.logs := Ninst.Hinv.inv (f := Devm.logs) q4
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
  have hshr : s3.output = t.output := Ninst.Hinv.inv (f := Devm.output) q4
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
  rw [show (sig =? sig) = 1 from by simp only [B256.eqCheck, ↓reduceIte]] at h_pfx1
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
          rw [B256.gtCheck, ite_eq_left h_gt] at h_flag
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
          rw [B256.gtCheck, ite_eq_right (fun h_gt => h_nlt h_gt)] at h_flag
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

/-- `run_body_of_run_nonpayable_frame` with the wrapper's log and output
silence.  A functional theorem that must relate a nonpayable endpoint's events
or returndata to the public frame's entry needs the same two projections the
dispatcher already carries. -/
theorem run_body_of_run_nonpayable_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧ s.memory = mid.memory ∧
      s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.Run fs sevm mid body r := by
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
  · exact absurd hrev not_run_revert
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
      · simp only [B256.eqCheck, hv, ↓reduceIte, ne_eq, not_true_eq_false] at hflag
    refine ⟨s3, hv, ?_, ?_, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)
    · exact (Line.of_inv Devm.logs (by line_inv) hline).trans
        (hpop.logs.trans hburn.logs)
    · exact (Line.of_inv Devm.output (by line_inv) hline).trans
        (hpop.output.trans hburn.output)

end DispatchLogFrame

end Blanc
