import Blanc.Lift.CallSiteChildren
import Blanc.ExecutionTraceCallOnly
import Blanc.ExecutionNoninterference
import Blanc.ExecutionCodeAt
import Blanc.LockExclusion
import Blanc.ExecutionReachable

/-!
# What a direct child frame runs, and what a spawn-free child keeps

* `Xinst.step_staticcall_spawn`: the `STATICCALL` sibling of `Xinst.step_call_spawn` — the frame a
  covered-fork `STATICCALL` spawns runs the callee's own code when the callee holds no delegation
  designator;
* `Exec.childFrames_code`: in a frame whose same-frame chain decodes only `CALL`/`STATICCALL`, a
  direct committed child at an address holding nonempty undelegated code at the frame's entry runs
  that code (nonempty code is preserved along the chain);
* `Exec.Frame.keeps_of_spawnFree`: a committed frame of code that spawns nothing at reached
  positions keeps the storage of every other address with code, and the code at every other address.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- **The frame a covered-fork `STATICCALL` spawns** runs the callee's own code when the callee
holds no delegation designator. -/
theorem Xinst.step_staticcall_spawn
    {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (hfork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm devm .staticcall = XStep.spawn f rsm) :
    ¬ isValidDelegation (devm.getCode f.inner.currentTarget) →
      f.inner.code = devm.getCode f.inner.currentTarget := by
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · simp only [Xinst.step, hsg, h1, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · simp only [Xinst.step, hsg, h1, h2, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h4 : d2.popToNat with err | ⟨ii, d4⟩
  · simp only [Xinst.step, hsg, h1, h2, h4, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h5 : d4.popToNat with err | ⟨isz, d5⟩
  · simp only [Xinst.step, hsg, h1, h2, h4, h5, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h6 : d5.popToNat with err | ⟨oi, d6⟩
  · simp only [Xinst.step, hsg, h1, h2, h4, h5, h6, Bind.bind, Except.bind,
      XStep.ofExcept, reduceCtorEq] at spawn
  rcases h7 : d6.popToNat with err | ⟨osz, d7⟩
  · simp only [Xinst.step, hsg, h1, h2, h4, h5, h6, h7, Bind.bind, Except.bind,
      XStep.ofExcept, reduceCtorEq] at spawn
  have hcode : (addAccessedAddress d7 callee).getCode callee =
      devm.getCode callee := by
    rw [addAccessedAddress_getCode]
    exact (Devm.popToNat_getCode h7).trans
      ((Devm.popToNat_getCode h6).trans
      ((Devm.popToNat_getCode h5).trans
      ((Devm.popToNat_getCode h4).trans
      ((Devm.popToAdr_getCode h2).trans
        (Devm.pop_getCode h1)))))
  simp only [Xinst.step, hsg, h1, h2, h4, h5, h6, h7, Bind.bind, Except.bind] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      intro notDelegation
      have hnd : ¬ isValidDelegation
          ((addAccessedAddress d7 callee).getCode callee) := by
        rw [hcode, ← hf.2.1]
        exact notDelegation
      have hdel := Blanc.GasSchedule.accessDelegation_of_not_delegation
        (gas := sevm.benvStat.rules.gas) hnd
      rw [hf.2.2, congrArg (fun t => t.2.2.1) hdel, hcode]
      exact congrArg devm.getCode hf.2.1.symm

/-- **What a direct child frame runs.**  In a frame whose same-frame chain decodes only
`CALL`/`STATICCALL`, a direct committed child at an address holding nonempty undelegated code at the
frame's entry runs that code. -/
theorem Exec.childFrames_code {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (hcall : ∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, pre, out, run⟩ N →
      ∀ x, Xinst.At N.sevm.code N.pc x → x = .call ∨ x = .staticcall)
    {a : Adr} (hne : (pre.getCode a).toList ≠ []) (hnd : ¬ isValidDelegation (pre.getCode a)) :
    ∀ c ∈ Exec.childFrames run, c.sevm.currentTarget = a → c.sevm.code = pre.getCode a := by
  intro c hc ht
  obtain ⟨N, f, rsm, pc', cevm, pp, hstep, henter, hsevm⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c hc
  have hNs : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq pp
  have hNc : N.devm.getCode a = pre.getCode a :=
    Exec.Deriv.ParentPrefix.codePreserve pp a hne
  obtain ⟨x, hxat, hxs, -⟩ := Evm.step_spawn_inv hstep
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv henter
  have htf : f.inner.currentTarget = a := by
    rw [← ht, hsevm, hcevm]; rfl
  have hcf : c.sevm.code = f.inner.code := by
    rw [hsevm, hcevm]; rfl
  have hfk : CoveredFork N.sevm.benvStat.fork := by rw [hNs]; exact hfork
  have hnd' : ¬ isValidDelegation (N.devm.getCode f.inner.currentTarget) := by
    rw [htf, hNc]; exact hnd
  rw [hcf]
  rcases hcall N pp x hxat with rfl | rfl
  · rw [(Xinst.step_call_spawn hfk hxs).2 hnd', htf, hNc]
  · rw [Xinst.step_staticcall_spawn hfk hxs hnd', htf, hNc]

/-- **A committed frame of spawn-free code keeps the storage of every other address with code and
the code of every other address.** -/
theorem Exec.Frame.keeps_of_spawnFree (c : Exec.Frame) (hpc : c.pc = 0)
    (hfork : CoveredFork c.sevm.benvStat.fork) (hsf : SpawnFreeReach c.sevm.code)
    {a : Adr} (hne : a ≠ c.sevm.currentTarget) :
    ((c.pre.getCode a).toList ≠ [] → ∀ key, (c.post.getStor a).get key = (c.pre.getStor a).get key) ∧
      c.post.getCode a = c.pre.getCode a := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hfork hsf hne ⊢
  subst hpc
  have hnil : Exec.rawFrameDescendants run = [] :=
    Exec.rawFrameDescendants_eq_nil_of_reach run (noPushBefore_zero _ _) hsf
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

end Blanc.Lift
