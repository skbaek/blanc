import Blanc.Lift.ChildFrameCode

/-!
# What a depth-`1` frame's children keep

Every spawn is depth-guarded (`Step.spawn_depth_lt`), so a frame at depth `0` enters no frame.

* `Exec.rawFrameDescendants_eq_nil_of_depth_zero`: a run at depth `0` has no raw descendant;
* `Exec.childFrames_depth`: every direct committed child sits strictly below its parent's depth
  and runs under a covered fork when the parent does;
* `Exec.Frame.keeps_of_depth_zero`: a committed frame at depth `0` keeps the storage of every
  other address with code and the code at every other address, whatever code it runs;
* `Exec.childFrames_keeps_of_depth_one`: so does every direct committed child of a depth-`1` frame.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- **A frame at depth `0` enters no frame**: every spawn sits strictly below its parent's
depth. -/
theorem Exec.rawFrameDescendants_eq_nil_of_depth_zero {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (h : sevm.depth = 0) :
    Exec.rawFrameDescendants run = [] := by
  revert h
  induction run with
  | halt _ => intro _; simp only [Exec.rawFrameDescendants]
  | cont _ _ ih => intro h; simpa only [Exec.rawFrameDescendants] using ih h
  | doneErr _ _ _ => intro _; simp only [Exec.rawFrameDescendants]
  | doneOk _ _ _ _ ih => intro h; simpa only [Exec.rawFrameDescendants] using ih h
  | runErr hstep _ _ _ _ =>
      intro h
      have := Step.spawn_depth_lt hstep
      omega
  | runOk hstep _ _ _ _ _ _ =>
      intro h
      have := Step.spawn_depth_lt hstep
      omega

/-- **Every direct committed child sits strictly below its parent's depth**, and runs under a
covered fork when the parent does. -/
theorem Exec.childFrames_depth {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ c ∈ Exec.childFrames run, c.sevm.depth < sevm.depth ∧ CoveredFork c.sevm.benvStat.fork := by
  intro c hc
  obtain ⟨N, f, rsm, pc', cevm, pp, hstep, henter, hsevm, -⟩ :=
    Exec.childFrames_spawnedAt_entry run (.refl _) c hc
  have hNs : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq pp
  have hlt := Step.spawn_depth_lt hstep
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv henter
  have hd : c.sevm.depth = f.inner.depth := by rw [hsevm, hcevm]; rfl
  refine ⟨by rw [hd, ← hNs]; exact hlt, ?_⟩
  rw [hsevm]
  exact Evm.step_spawn_child_fork hstep henter (by rw [hNs]; exact hfork)

/-- **A committed frame at depth `0` keeps the storage of every other address with code and the
code at every other address**, whatever code it runs. -/
theorem Exec.Frame.keeps_of_depth_zero (c : Exec.Frame) (hfork : CoveredFork c.sevm.benvStat.fork)
    (hd : c.sevm.depth = 0) {a : Adr} (hne : a ≠ c.sevm.currentTarget) :
    ((c.pre.getCode a).toList ≠ [] → ∀ key, (c.post.getStor a).get key = (c.pre.getStor a).get key) ∧
      c.post.getCode a = c.pre.getCode a := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hfork hd hne ⊢
  have hnil : Exec.rawFrameDescendants run = [] :=
    Exec.rawFrameDescendants_eq_nil_of_depth_zero run hd
  have hroots : ∀ r ∈ Exec.rawFrameRoots run, r.sevm.currentTarget ≠ a := by
    intro r hr
    simp only [Exec.rawFrameRoots, hnil, List.mem_singleton] at hr
    subst hr
    exact fun h => hne h.symm
  refine ⟨fun hcode key => ?_, ?_⟩
  · exact Exec.committedCell_eq_of_noRetainedWriteTo run committed hfork a key hcode
      (Exec.noRetainedWriteTo_of_frame_owners_ne run a key hroots)
  · have hrel := (Exec.codeAt_avoid run hfork (fun r hr _ => hroots r hr)).1
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact hrel

/-- **Every direct committed child of a depth-`1` frame keeps the storage of every other address
with code and the code at every other address.** -/
theorem Exec.childFrames_keeps_of_depth_one {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (hd : sevm.depth = 1) :
    ∀ c ∈ Exec.childFrames run, ∀ a, a ≠ c.sevm.currentTarget →
      ((c.pre.getCode a).toList ≠ [] →
        ∀ key, (c.post.getStor a).get key = (c.pre.getStor a).get key) ∧
        c.post.getCode a = c.pre.getCode a := by
  intro c hc a hne
  obtain ⟨hlt, hcf⟩ := Exec.childFrames_depth run hfork c hc
  exact Exec.Frame.keeps_of_depth_zero c hcf (by omega) hne

end Blanc.Lift
