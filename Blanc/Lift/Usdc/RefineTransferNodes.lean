import Blanc.Lift.Usdc.RefineTransferDispatch
import Blanc.Lift.ReachDispatch

/-!
# The transfer and allowance family makes no external call

A frame of the implementation whose selector is one of the family's five reaches, through the
dispatcher, a selector wrapper whose closure (`familyFree`) is free of external instructions; so no
node of its own chain decodes one (`reach_of_parentPrefix`, `Reach.false_of_execFree`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

/-- The family's wrappers, their callees and the dispatcher's revert entry. -/
def familyFree : List Nat := [7, 12, 13, 19, 36, 37, 58, 68, 71, 81, 83, 92, 93, 96, 98, 99, 100,
  102, 115, 119, 144, 145, 165, 175, 178]

theorem familyFree_execFree : ExecFreeSet cert.prog familyFree = true := by decide +kernel

theorem Reach.ite_left {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {d : Devm} {K : List SFunc} {T : Conf} {c : Prop} [Decidable c] {f g : SFunc} (hc : c)
    (h : Reach P fs sevm ⟨d, if c then f else g, K⟩ T) : Reach P fs sevm ⟨d, f, K⟩ T := by
  rwa [ite_eq_left hc] at h

theorem Reach.ite_right {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {d : Devm} {K : List SFunc} {T : Conf} {c : Prop} [Decidable c] {f g : SFunc} (hc : ¬ c)
    (h : Reach P fs sevm ⟨d, if c then f else g, K⟩ T) : Reach P fs sevm ⟨d, g, K⟩ T := by
  rwa [ite_eq_right hc] at h

/-- One straight-line step of a reach `h` to the external instruction `t`. -/
macro "rstep " h:ident t:ident : tactic => `(tactic| first
  | (have h' := rr_dest $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h')
  | (have h' := rr_next $h $t; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepX ‹CoveredFork _› (StepIn.toRun hd) rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd))

/-- A conditional jump of the reach; an arm inside `familyFree` closes. -/
macro "rbranch " h:ident t:ident : tactic => `(tactic|
  (have h' := rr_branch $h $t; clear $h; rcases h' with ⟨_, _, $h:ident⟩ | ⟨_, _, $h:ident⟩ <;>
    try (exact (Reach.false_of_execFree familyFree_execFree $h $t (by decide)
      (fun _ hs => absurd hs List.not_mem_nil)).elim)))

/-- One dispatcher comparison of the reach on a known selector; the reach then closes as soon
as it stands in `familyFree`. -/
macro "rdisp " h:ident t:ident : tactic => `(tactic| first
  | (exact (Reach.false_of_execFree familyFree_execFree $h $t (by decide)
      (fun _ hs => absurd hs List.not_mem_nil)).elim)
  | (have h' := rr_cmp_gt StepIn.toRun $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (replace $h:ident := Reach.ite_left (by decide) $h)
     | (replace $h:ident := Reach.ite_right (by decide) $h))
  | (have h' := rr_cmp_eq StepIn.toRun rfl $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (replace $h:ident := Reach.ite_left (by decide) $h)
     | (replace $h:ident := Reach.ite_right (by decide) $h))
  | (have h' := rr_dest $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h'))

/-- The five selectors of the family. -/
def famSelectors : List B256 := [0xa9059cbb, 0x23b872dd, 0x095ea7b3, 0x39509351, 0xa457c2d7]

/-- **No node of a family frame's own chain decodes an external instruction.** -/
theorem family_noExec {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm ∈ famSelectors) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N hN x hat
  obtain ⟨κ, reach, okN⟩ := reach_of_parentPrefix cert_check rfl codeEq fork hN
  obtain ⟨g, hg, -⟩ := okN.tree_of_exec hat
  have t : AtExec (κ.conf N.devm) := ⟨x, g, hg⟩
  generalize κ.conf N.devm = T at reach t
  have h : Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) cert.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, t_0000_c0, []⟩ T := by
    rw [← St.self rfl rfl]
    exact reach
  clear reach okN hg hat
  repeat rstep h t
  rbranch h t
  repeat rstep h t
  rbranch h t
  iterate 4 rstep h t
  rw [selector_word] at h
  simp only [famSelectors, List.mem_cons, List.not_mem_nil, or_false] at sel
  rcases sel with s | s | s | s | s <;> rw [s] at h <;> repeat rdisp h t

end Blanc.Lift.Usdc
