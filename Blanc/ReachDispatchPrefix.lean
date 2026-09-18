import Blanc.RunPrefix
import Blanc.CommonProofs

/-!
Contract-neutral sorted-tree dispatcher reachability with the loose walk
prefix exposed.

`reach_of_dispatch_logs` is the inline-revert dispatcher's log/output-silent
factorization (`CommonProofs`' dispatcher family), generalized with the
`Func.RunPrefix` conjunct the DRIP prefix transport consumes: besides the
selected body's entry state and silence facts, it exposes the gas-free walk
prefix from the dispatcher's entry to that state, with source-path
accumulation. The generalization cannot live in `Blanc.CommonProofs` (which
cannot import `Blanc.RunPrefix`: hard import cycle through `GasErasure`), so
the pair moved here, above both — the single canonical home.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree
open scoped LogOutputHinv

/-! `dispatch`'s inline-revert leaves need the same log/output frame as the
indexed-fallback dispatcher above.  These three mirror
`reach_of_dispatchWith_*_logs` at the simpler leaf, so a receive-aware
contract whose dispatcher reverts inline can carry event chronology from the
public frame's entry into the selected body. -/

private lemma reach_of_dispatch_leaf_logs {sig w : B256} {f p : Func}
    {c : List Func} {e : Sevm} {s r : Devm} {ws : Stack}
    {path : Prog.SourcePath}
    (h_mem : (sig, f) ∈ [(w, p)])
    (h_pfx : sig :: ws <<+ s.stack) :
    Func.Run c e s (dispatch (DispatchTree.leaf w p)) r →
    ∃ s' target, (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      s.logs = s'.logs ∧ s.output = s'.output ∧
      Func.RunPrefix c e path s (dispatch (DispatchTree.leaf w p)) target s' f ∧
      Func.Run c e s' f r := by
  have h_eq : (sig, f) = (w, p) := List.mem_singleton.mp h_mem
  injection h_eq with h_sig h_f
  subst h_sig
  subst h_f
  cases path with
  | mk k steps =>
    func_execute 2
    intro h₂
    have h_pfx1 : (sig =? sig) :: ws <<+ s₁.stack := by
      generalize_line_prefix
    rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at h_pfx1
    have hfree : Line.gasFree [pushB256 sig, eq] = true := by
      simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree, Rinst.gasFree,
        Bool.true_and]
    have hline : Func.RunPrefix c e ⟨k, steps⟩ s
        (dispatch (DispatchTree.leaf sig f))
        ⟨k, steps ++ [.rest, .rest]⟩ s₁ (.branch .revert f) :=
      Func.RunPrefix.line h₁ hfree
    rcases Func.RunPrefix.of_run_branch (k := k)
        (steps := steps ++ [.rest, .rest]) h₂ with
        ⟨s₂, h_pop, h_runf, hbranch⟩ |
        ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_runf, hbranch⟩
    · exact absurd h_runf not_run_revert
    · rcases popBurn_pref h_pop h_pfx1 with ⟨-, h_pfx2⟩
      refine ⟨s₃, _, ?_, ?_, ?_, ?_, ?_, hline.trans hbranch, h_runf⟩
      · rw [← h_burn.stack]
        exact h_pfx2
      · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
          (h_pop.state.trans h_burn.state)
      · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
          (h_pop.memory.trans h_burn.memory)
      · exact (Line.of_inv Devm.logs (by line_inv) h₁).trans
          (h_pop.logs.trans h_burn.logs)
      · exact (Line.of_inv Devm.output (by line_inv) h₁).trans
          (h_pop.output.trans h_burn.output)

private theorem reach_of_dispatch_build_logs :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {c : List Func} {e : Sevm} {s r : Devm} {ws : Stack}
      {path : Prog.SourcePath},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (sig :: ws <<+ s.stack) →
      Func.Run c e s (dispatch (DispatchTree.build n xs)) r →
      ∃ s' target, (ws <<+ s'.stack) ∧ s.state = s'.state ∧
        s.memory = s'.memory ∧ s.logs = s'.logs ∧ s.output = s'.output ∧
        Func.RunPrefix c e path s (dispatch (DispatchTree.build n xs))
          target s' f ∧
        Func.Run c e s' f r := by
  intro n
  induction n with
  | zero =>
    intro xs sig f c e s r ws path h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatch_leaf_logs h_mem h_pfx
    · intro _
      exfalso
      simp only [List.length_cons] at h_len
      omega
  | succ n ih =>
    intro xs sig f c e s r ws path h_sorted h_len h_mem h_pfx
    rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases h_mem
    · exact reach_of_dispatch_leaf_logs h_mem h_pfx
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
      cases path with
      | mk k steps =>
        func_execute 3
        intro h₂
        have h_pfx1 :
            (leftmostFsig (DispatchTree.build n
              (((w, p) :: y :: ys).drop
                ((((w, p) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: ws <<+ s₁.stack := by
          generalize_line_prefix
        rw [h_drop, DispatchTree.leftmostFsig_build] at h_pfx1
        have hfree : Line.gasFree [dup 0,
            pushB256 (leftmostFsig (DispatchTree.build n
              (((w, p) :: y :: ys).drop
                ((((w, p) :: y :: ys).length + 1) / 2)))), gt] = true := by
          simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree, Rinst.gasFree,
            Bool.true_and]
        have hline : Func.RunPrefix c e ⟨k, steps⟩ s
            (dispatch (DispatchTree.build (n + 1) ((w, p) :: y :: ys)))
            ⟨k, steps ++ [.rest, .rest, .rest]⟩ s₁
            (.branch
              (dispatch (DispatchTree.build n
                (((w, p) :: y :: ys).drop
                  ((((w, p) :: y :: ys).length + 1) / 2))))
              (dispatch (DispatchTree.build n
                (((w, p) :: y :: ys).take
                  ((((w, p) :: y :: ys).length + 1) / 2))))) :=
          Func.RunPrefix.line h₁ hfree
        rcases Func.RunPrefix.of_run_branch (k := k)
            (steps := steps ++ [.rest, .rest, .rest]) h₂ with
            ⟨s₂, h_pop, h_run', hbranch⟩ |
            ⟨v, s₂, s₃, h_ne, h_pop, h_burn, h_run', hbranch⟩
        ·
          rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
          have h_le : z.fst ≤ sig := by
            rw [← B256.not_lt]
            intro h_lt
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
                rw [h_drop]
                exact List.mem_cons_self ..
              have h_lt := DispatchTree.fst_lt_of_sorted_append
                h_sorted_split h_in h_z
              have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
              have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
              omega
            · exact h_in
          rcases ih (path := ⟨k, (steps ++ [.rest, .rest, .rest]) ++
              [.branchLeft]⟩) h_sorted_drop h_drop_len h_mem_drop h_pfx2
              h_run' with
            ⟨s', _, h_s', h_st, h_mm, h_logs, h_output, hprefix, h_rf⟩
          refine ⟨s', _, h_s', ?_, ?_, ?_, ?_, hline.trans (hbranch.trans hprefix),
            h_rf⟩
          · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
              (h_pop.state.trans h_st)
          · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
              (h_pop.memory.trans h_mm)
          · exact (Line.of_inv Devm.logs (by line_inv) h₁).trans
              (h_pop.logs.trans h_logs)
          · exact (Line.of_inv Devm.output (by line_inv) h₁).trans
              (h_pop.output.trans h_output)
        ·
          rcases popBurn_pref h_pop h_pfx1 with ⟨h_flag, h_pfx2⟩
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
                rw [← h_drop]
                exact h_sorted_drop
              have h_le := DispatchTree.fst_le_of_sorted_mem h_sorted_zzs h_in
              have h1 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
              have h2 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
              omega
          rw [h_burn.stack] at h_pfx2
          rcases ih (path := ⟨k, (steps ++ [.rest, .rest, .rest]) ++
              [.branchRight]⟩) h_sorted_take h_take_len h_mem_take h_pfx2
              h_run' with
            ⟨s', _, h_s', h_st, h_mm, h_logs, h_output, hprefix, h_rf⟩
          refine ⟨s', _, h_s', ?_, ?_, ?_, ?_, hline.trans (hbranch.trans hprefix),
            h_rf⟩
          · exact (Line.of_inv Devm.state (by line_inv) h₁).trans
              (h_pop.state.trans (h_burn.state.trans h_st))
          · exact (Line.of_inv Devm.memory (by line_inv) h₁).trans
              (h_pop.memory.trans (h_burn.memory.trans h_mm))
          · exact (Line.of_inv Devm.logs (by line_inv) h₁).trans
              (h_pop.logs.trans (h_burn.logs.trans h_logs))
          · exact (Line.of_inv Devm.output (by line_inv) h₁).trans
              (h_pop.output.trans (h_burn.output.trans h_output))

/-- `reach_of_dispatch` with the dispatcher-entry log and output carried to
the selected body, plus the loose gas-free walk prefix reaching the body's
entry state.  The body may append logs or write output afterward; this
theorem only states that inline-revert dispatch itself is log- and
output-silent. -/
theorem reach_of_dispatch_logs {funcs : List (B256 × Func)}
    {sig : B256} {f : Func} {c : List Func} {e : Sevm} {s r : Devm}
    {ws : Stack} {path : Prog.SourcePath}
    (h_sorted : DispatchTree.sorted funcs = true)
    (h_mem : (sig, f) ∈ funcs)
    (h_pfx : sig :: ws <<+ s.stack)
    (h_run : Func.Run c e s (dispatch (DispatchTree.ofSorted funcs)) r) :
    ∃ s' target, (ws <<+ s'.stack) ∧ s.state = s'.state ∧ s.memory = s'.memory ∧
      s.logs = s'.logs ∧ s.output = s'.output ∧
      Func.RunPrefix c e path s (dispatch (DispatchTree.ofSorted funcs))
        target s' f ∧
      Func.Run c e s' f r :=
  reach_of_dispatch_build_logs h_sorted (Nat.le_succ _) h_mem h_pfx h_run

end Blanc
