import Blanc.LidoCircuitBreakerSites

/-!
Settlement-retained owner closure for the exact installed Lido CircuitBreaker
runtime.  This module is deliberately contract-local: it composes the common
interpreter/occurrence substrate with the runtime's reviewed external-edge
boundary, without importing another contract family.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst

/-- Proof-indexed closure consumed by `lift_core`.  Installation is carried
separately from direct code identity: the latter is required only when the
current frame owns CircuitBreaker storage. -/
def Exec.CoreRuntimeOwnerClosed (dp : DeployParams) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out)
    (_committed : Execution.commits out = true),
    Prog.At (runtime dp) ca pc sevm pre →
    (sevm.currentTarget = ca → sevm.codeAddress = some ca) →
    ∀ frame ∈ Exec.committedFrames run,
      frame.sevm.currentTarget = ca →
        frame.exactInvocation (runtime dp) ca ca

/-- CALL and STATICCALL initialize a spawned child with its target's direct
code address, including the same-target case where the generic away-from-parent
lemma intentionally does not apply. -/
private theorem directExternalStep_codeAddress
    {sevm : Sevm} {devm : Devm} {x : Jaune.Xinst}
    {f : Jaune.Frame} {rsm : Resume}
    (direct : x = Jaune.Xinst.call ∨ x = Jaune.Xinst.statcall)
    (spawn : Jaune.Xinst.step sevm devm x = Jaune.XStep.spawn f rsm) :
    f.inner.codeAddress = some f.inner.currentTarget := by
  rcases direct with rfl | rfl
  · simp only [Jaune.Xinst.step, Bind.bind, Except.bind, Except.assert] at spawn
    repeat' split at spawn
    all_goals simp only [Jaune.XStep.ofExcept, reduceCtorEq] at spawn
    all_goals first
      | cases spawn
      | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at spawn
        repeat' split at spawn
        all_goals
          simp only [Jaune.XStep.ofExcept, Jaune.XStep.spawn.injEq,
            reduceCtorEq] at spawn
        all_goals obtain ⟨rfl, rfl⟩ := spawn
        all_goals rfl
  · simp only [Jaune.Xinst.step, Bind.bind, Except.bind] at spawn
    repeat' split at spawn
    all_goals simp only [Jaune.XStep.ofExcept, reduceCtorEq] at spawn
    all_goals first
      | cases spawn
      | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at spawn
        repeat' split at spawn
        all_goals
          simp only [Jaune.XStep.ofExcept, Jaune.XStep.spawn.injEq,
            reduceCtorEq] at spawn
        all_goals obtain ⟨rfl, rfl⟩ := spawn
        all_goals rfl

/-- A direct CALL back into the current target loads that target's own code
when the installed account is not an EOA delegation designator. -/
private theorem callStep_sameTarget_code
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (spawn : Jaune.Xinst.step sevm devm .call = Jaune.XStep.spawn f rsm)
    (sameTarget : f.inner.currentTarget = sevm.currentTarget)
    (notDelegation :
      ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · simp [Jaune.Xinst.step, h1, Jaune.XStep.ofExcept] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · simp [Jaune.Xinst.step, h1, h2, Jaune.XStep.ofExcept] at spawn
  rcases h3 : d2.pop with err | ⟨value, d3⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, Jaune.XStep.ofExcept] at spawn
  rcases h4 : d3.popToNat with err | ⟨ii, d4⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, Jaune.XStep.ofExcept] at spawn
  rcases h5 : d4.popToNat with err | ⟨isz, d5⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, h5,
      Jaune.XStep.ofExcept] at spawn
  rcases h6 : d5.popToNat with err | ⟨oi, d6⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, h5, h6,
      Jaune.XStep.ofExcept] at spawn
  rcases h7 : d6.popToNat with err | ⟨osz, d7⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, h5, h6, h7,
      Jaune.XStep.ofExcept] at spawn
  have hcode : (addAccessedAddress d7 callee).getCode callee =
      devm.getCode callee := by
    rw [addAccessedAddress_getCode]
    exact (Devm.popToNat_getCode h7).trans
      ((Devm.popToNat_getCode h6).trans
      ((Devm.popToNat_getCode h5).trans
      ((Devm.popToNat_getCode h4).trans
      ((Devm.pop_getCode h3).trans
      ((Devm.popToAdr_getCode h2).trans
        (Devm.pop_getCode h1))))))
  simp only [Jaune.Xinst.step, h1, h2, h3, h4, h5, h6, h7,
    Bind.bind, Except.bind, Except.assert] at spawn
  repeat' split at spawn
  all_goals simp only [Jaune.XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      have hcallee : callee = sevm.currentTarget :=
        hf.2.1.symm.trans sameTarget
      have hnd : ¬ isValidDelegation
          ((addAccessedAddress d7 callee).getCode callee) := by
        rw [hcode, hcallee, ← sameTarget]
        exact notDelegation
      have hdel := accessDelegation_of_not_delegation hnd
      rw [hf.2.2, congrArg (fun t => t.2.2.1) hdel, hcode]
      exact congrArg devm.getCode hf.2.1.symm

/-- STATICCALL has the same direct-code property as CALL. -/
private theorem statcallStep_sameTarget_code
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (spawn : Jaune.Xinst.step sevm devm .statcall =
      Jaune.XStep.spawn f rsm)
    (sameTarget : f.inner.currentTarget = sevm.currentTarget)
    (notDelegation :
      ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · simp [Jaune.Xinst.step, h1, Jaune.XStep.ofExcept] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · simp [Jaune.Xinst.step, h1, h2, Jaune.XStep.ofExcept] at spawn
  rcases h3 : d2.popToNat with err | ⟨ii, d3⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, Jaune.XStep.ofExcept] at spawn
  rcases h4 : d3.popToNat with err | ⟨isz, d4⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, Jaune.XStep.ofExcept] at spawn
  rcases h5 : d4.popToNat with err | ⟨oi, d5⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, h5,
      Jaune.XStep.ofExcept] at spawn
  rcases h6 : d5.popToNat with err | ⟨osz, d6⟩
  · simp [Jaune.Xinst.step, h1, h2, h3, h4, h5, h6,
      Jaune.XStep.ofExcept] at spawn
  have hcode : (addAccessedAddress d6 callee).getCode callee =
      devm.getCode callee := by
    rw [addAccessedAddress_getCode]
    exact (Devm.popToNat_getCode h6).trans
      ((Devm.popToNat_getCode h5).trans
      ((Devm.popToNat_getCode h4).trans
      ((Devm.popToNat_getCode h3).trans
      ((Devm.popToAdr_getCode h2).trans
        (Devm.pop_getCode h1)))))
  simp only [Jaune.Xinst.step, h1, h2, h3, h4, h5, h6,
    Bind.bind, Except.bind] at spawn
  repeat' split at spawn
  all_goals simp only [Jaune.XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      have hcallee : callee = sevm.currentTarget :=
        hf.2.1.symm.trans sameTarget
      have hnd : ¬ isValidDelegation
          ((addAccessedAddress d6 callee).getCode callee) := by
        rw [hcode, hcallee, ← sameTarget]
        exact notDelegation
      have hdel := accessDelegation_of_not_delegation hnd
      rw [hf.2.2, congrArg (fun t => t.2.2.1) hdel, hcode]
      exact congrArg devm.getCode hf.2.1.symm

/-- The reviewed direct external edges load the current target's own code in
the same-target case. -/
private theorem directExternalStep_sameTarget_code
    {sevm : Sevm} {devm : Devm} {x : Jaune.Xinst}
    {f : Jaune.Frame} {rsm : Resume}
    (direct : x = Jaune.Xinst.call ∨ x = Jaune.Xinst.statcall)
    (spawn : Jaune.Xinst.step sevm devm x = Jaune.XStep.spawn f rsm)
    (sameTarget : f.inner.currentTarget = sevm.currentTarget)
    (notDelegation :
      ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases direct with rfl | rfl
  · exact callStep_sameTarget_code spawn sameTarget notDelegation
  · exact statcallStep_sameTarget_code spawn sameTarget notDelegation

/-- One successful driver step preserves the installed runtime account. -/
private theorem step_ok_runtimeCode_eq
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {xl : Xlot}
    (hxl : Xlot.Rel Devm.CodePreserve xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, pre⟩) xl (.ok post))
    (hcode : some (pre.getCode ca).toList = Prog.compile (runtime dp)) :
    post.getCode ca = pre.getCode ca := by
  have hne : (pre.getCode ca).toList ≠ [] := fun hempty =>
    Prog.compile_ne_nil (hcode.symm.trans (congrArg some hempty))
  exact Evm.step_effect codePreserve_refl_trans.1
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect
    Linst.codePreserve_effect hxl hrun ca hne

/-- Failed executions have no committed-frame closure obligation. -/
theorem Exec.CoreRuntimeOwnerClosed.error
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre (.error error) := by
  intro run committed
  simp [Execution.commits] at committed

/-- A successful nonrecursive step in a foreign frame contributes no owner
frame; every retained descendant is supplied by the continuation. -/
theorem Exec.CoreRuntimeOwnerClosed.nextNone
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreRuntimeOwnerClosed dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre out := by
  intro run committed installed direct frame member owner
  have installedInter : Prog.At (runtime dp) ca
      (pc + n.size) sevm inter := by
    refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
    rw [step_ok_runtimeCode_eq (dp := dp) (ca := ca) (xl := .none) trivial
      (by
        have hrun : Step.Run (Evm.step ⟨pc, sevm, pre⟩)
            .none (.ok inter) := by
          rw [Evm.step_next hat]
          exact hstep
        exact hrun) installed.1]
    exact installed.1
  have tail := ih next committed installedInter
    (fun htarget => (hforeign htarget).elim)
  cases hs : Ninst.step ⟨pc, sevm, pre⟩ n with
  | halt execution =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      exact False.elim (Ninst.step_ne_halt_ok hs)
  | cont pc' actual =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      have hpc : pc' = pc + n.size := Ninst.step_cont_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + n.size) inter := by
        rw [Evm.step_next hat]
        exact hs
      have hcanonical : run = Exec.cont hevm next := Exec.unique _ _
      subst run
      unfold Exec.committedFrames at member
      rw [dif_pos committed] at member
      simp only [List.mem_cons] at member
      rcases member with rfl | descendant
      · exact (hforeign owner).elim
      · apply tail frame
        · unfold Exec.committedFrames
          rw [dif_pos committed]
          simp only [List.mem_cons]
          exact Or.inr (by
            simpa only [Exec.descendantFrames] using descendant)
        · exact owner

  | spawn spawned resume pc' =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨result, hframe, hresume⟩
      have hpc : pc' = pc + n.size := Ninst.step_spawn_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .spawn spawned resume (pc + n.size) := by
        rw [Evm.step_next hat]
        exact hs
      have hdone : ∃ result',
          spawned.enter = .done result' ∧ result = result' := by
        unfold RunFrame at hframe
        rcases henter : spawned.enter with result' | childEvm
        · rw [henter] at hframe
          exact ⟨result', rfl, hframe.2⟩
        · rw [henter] at hframe
          rcases hframe with ⟨raw, hnone, _⟩
          cases hnone
      rcases hdone with ⟨result', henter, hresult⟩
      subst result
      let canonical : Exec pc sevm pre out :=
        Exec.doneOk hevm henter hresume.symm next
      have hcanonical : run = canonical := Exec.unique _ _
      subst run
      unfold Exec.committedFrames at member
      rw [dif_pos committed] at member
      simp only [List.mem_cons] at member
      rcases member with rfl | descendant
      · exact (hforeign owner).elim
      · apply tail frame
        · unfold Exec.committedFrames
          rw [dif_pos committed]
          simp only [List.mem_cons]
          exact Or.inr (by
            simpa only [canonical, Exec.descendantFrames] using descendant)
        · exact owner

/-- Foreign jump bookkeeping adds no frame; the continuation owns every
retained descendant. -/
theorem Exec.CoreRuntimeOwnerClosed.jump
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {j : Jinst}
    {pc' : Nat} {inter : Devm} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (hstep : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreRuntimeOwnerClosed dp ca pc' sevm inter out) :
    Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre out := by
  intro run committed installed direct frame member owner
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter := by
    rw [Evm.step_jump hat]
    exact congrArg Step.ofJump hstep
  have hcanonical : run = Exec.cont hevm next := Exec.unique _ _
  subst run
  have hframe := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ j
  rw [hstep] at hframe
  have installedInter : Prog.At (runtime dp) ca pc' sevm inter := by
    refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
    rw [show inter.getCode ca = pre.getCode ca from
      (hframe.getCode ca).symm]
    exact installed.1
  have tail := ih next committed installedInter
    (fun htarget => (hforeign htarget).elim)
  unfold Exec.committedFrames at member
  rw [dif_pos committed] at member
  simp only [List.mem_cons] at member
  rcases member with rfl | descendant
  · exact (hforeign owner).elim
  · apply tail frame
    · unfold Exec.committedFrames
      rw [dif_pos committed]
      simp only [List.mem_cons]
      exact Or.inr (by
        simpa only [Exec.descendantFrames] using descendant)
    · exact owner

/-- A foreign terminal frame cannot itself own CircuitBreaker storage and has
no descendants. -/
theorem Exec.CoreRuntimeOwnerClosed.last
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst}
    {out : Execution}
    (hat : Linst.At sevm.code pc l)
    (hstep : Linst.Run sevm pre l out)
    (hforeign : sevm.currentTarget ≠ ca) :
    Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre out := by
  intro run committed installed direct frame member owner
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .halt out := by
    rw [Evm.step_last hat]
    exact congrArg Step.halt hstep
  have hcanonical : run = Exec.halt hevm := Exec.unique _ _
  subst run
  unfold Exec.committedFrames at member
  rw [dif_pos committed] at member
  simp only [Exec.descendantFrames, List.mem_singleton] at member
  subst frame
  exact (hforeign owner).elim

/-- A recursive foreign step transports installation into both the entered
child and the parent continuation.  A child returning to the CircuitBreaker
owner is direct by the landed common spawn theorem. -/
theorem Exec.CoreRuntimeOwnerClosed.nextSome
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n
      (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreRuntimeOwnerClosed dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreRuntimeOwnerClosed dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hstep
  | push xs hxs =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
  | exec x =>
      intro run committed installed direct frame member owner
      have hxrun := XStep.run_toStep.mp hstep
      cases hs : Xinst.step sevm pre x with
      | done execution =>
          simp [hs, XStep.Run] at hxrun
      | spawn spawned resume =>
          simp only [hs, XStep.Run] at hxrun
          obtain ⟨result, hframe, hresume⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at hresume
          | ok settled =>
              have henter := (RunFrame.some_inv hframe).1
              have hsettle := (RunFrame.some_inv hframe).2
              have hevm : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn spawned resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, hs, XStep.toStep]
              have hr : resume.run (spawned.settle raw) = .ok inter := by
                rw [← hsettle]
                exact hresume.symm
              let canonical : Exec pc sevm pre out :=
                Exec.runOk hevm henter child hr next
              have hcanonical : run = canonical := Exec.unique _ _
              subst run
              obtain ⟨hpc0, hgc, hsrc⟩ :=
                Evm.step_spawn_child hevm henter
              have hchildAt : Prog.At (runtime dp) ca
                  cevm.pc cevm.sta cevm.dyna := by
                refine ⟨?_, fun htarget => ⟨?_, hpc0⟩⟩
                · rw [hgc ca]
                  exact installed.1
                · have hne' :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [htarget]
                    exact hforeign
                  have hcode := hsrc hne'
                    (by rw [htarget]
                        exact not_empty_of_compile installed.1)
                    (by rw [htarget]
                        exact not_delegation_of_compile installed.1)
                  rw [hcode, htarget]
                  exact installed.1
              have hchildDirect : cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro htarget
                have hinnerTarget :
                    spawned.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget henter]
                  exact htarget
                have hparentNe :
                    sevm.currentTarget ≠ spawned.inner.currentTarget := by
                  rw [hinnerTarget]
                  exact hforeign
                have hnonempty :
                    pre.getCode spawned.inner.currentTarget ≠ .empty := by
                  rw [hinnerTarget]
                  exact not_empty_of_compile installed.1
                have hcadr :=
                  Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
                    hs hparentNe hnonempty
                rcases Frame.enter_run_inv henter with
                  ⟨benv, htransfer, hinit⟩
                have hcadrInit :=
                  congrArg (fun e : Evm => e.sta.codeAddress) hinit
                dsimp [initEvm, initSevm, Msg.withBenv] at hcadrInit
                rw [hcadrInit, hcadr, hinnerTarget]
              have hchildRel :
                  Xlot.Rel Devm.CodePreserve (.some ⟨cevm, raw⟩) :=
                Exec.effect codePreserve_refl_trans.1
                  codePreserve_refl_trans.2
                  Ninst.codePreserve_effectRec
                  Jinst.codePreserve_effect
                  Linst.codePreserve_effect child
              have installedInter : Prog.At (runtime dp) ca
                  (pc + 1) sevm inter := by
                refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
                rw [step_ok_runtimeCode_eq (dp := dp) (ca := ca) hchildRel
                  (by
                    rw [hevm]
                    exact ⟨spawned.settle raw, RunFrame.of_run henter,
                      hr.symm⟩) installed.1]
                exact installed.1
              have tail := ihNext next committed installedInter
                (fun htarget => (hforeign htarget).elim)
              unfold Exec.committedFrames at member
              rw [dif_pos committed] at member
              simp only [List.mem_cons] at member
              rcases member with rfl | descendant
              · exact (hforeign owner).elim
              · simp only [canonical, Exec.descendantFrames] at descendant
                split at descendant
                next childSettles =>
                  have childCommits :=
                    Frame.raw_commits_of_settlementCommits childSettles
                  have childClosed := ihChild child childCommits hchildAt
                    hchildDirect
                  simp only [List.mem_append, List.mem_cons] at descendant
                  rcases descendant with (rfl | hchild) | hnext
                  · apply childClosed (Exec.Frame.ofRun child childCommits)
                    · unfold Exec.committedFrames
                      rw [dif_pos childCommits]
                      simp
                    · simpa only [Exec.Frame.ofRun] using owner
                  · apply childClosed frame
                    · unfold Exec.committedFrames
                      rw [dif_pos childCommits]
                      simp [hchild]
                    · exact owner
                  · apply tail frame
                    · unfold Exec.committedFrames
                      rw [dif_pos committed]
                      simp only [List.mem_cons]
                      exact Or.inr hnext
                    · exact owner
                next childDoesNotSettle =>
                  simp only [List.nil_append] at descendant
                  apply tail frame
                  · unfold Exec.committedFrames
                    rw [dif_pos committed]
                    simp only [List.mem_cons]
                    exact Or.inr descendant
                  · exact owner

/-- Descendant closure inside one exact runtime frame.  Same-frame recursion
keeps a `ParentPrefix` from the exact root, so every reached external opcode is
classified structurally before the strong-depth hypothesis is applied to its
entered child. -/
private theorem Exec.runtimeDescendantOwnerClosure :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out),
      ∀ {dp : DeployParams} {ca : Adr}
        {rootPc : Nat} {rootPre : Devm} {rootOut : Execution}
        {rootRun : Exec rootPc sevm rootPre rootOut},
        (⟨rootPc, sevm, rootPre, rootOut, rootRun⟩ : Exec.Deriv).exactInvocation
          (runtime dp) ca ca →
        Exec.Deriv.ParentPrefix
          ⟨rootPc, sevm, rootPre, rootOut, rootRun⟩
          ⟨pc, sevm, pre, out, run⟩ →
        some (pre.getCode ca).toList = (runtime dp).compile →
        ForallDeeperAt sevm.depth ca (runtime dp)
          (fun pc s d e _ => Exec.CoreRuntimeOwnerClosed dp ca pc s d e) →
        ∀ frame ∈ Exec.descendantFrames run,
          frame.sevm.currentTarget = ca →
            frame.exactInvocation (runtime dp) ca ca := by
  intro pc sevm pre out run
  induction run
  case halt curPc s d e hstep =>
      intro dp ca rootPc rootPre rootOut rootRun invocation sameFrame installed hdeeper
        frame member owner
      simp [Exec.descendantFrames] at member
  case cont curPc s d nextPc nextPre e hstep next ih =>
      intro dp ca rootPc rootPre rootOut rootRun invocation sameFrame installed hdeeper
        frame member owner
      have hcode : d.getCode ca = nextPre.getCode ca := by
        symm
        exact step_ok_runtimeCode_eq (dp := dp) (ca := ca) (xl := .none)
          trivial (by rw [hstep]; exact ⟨rfl, rfl⟩) installed
      have installedNext : some (nextPre.getCode ca).toList =
          (runtime dp).compile := by
        rw [← hcode]
        exact installed
      let edge : Exec.Deriv.ParentStep
          ⟨nextPc, s, nextPre, e, next⟩
          ⟨curPc, s, d, e, Exec.cont hstep next⟩ :=
        .cont hstep next
      exact ih invocation (sameFrame.snoc edge) installedNext hdeeper frame
        (by simpa only [Exec.descendantFrames] using member) owner
  case doneErr curPc s d spawned resume nextPc settled e hstep henter hresume =>
      intro dp ca rootPc rootPre rootOut rootRun invocation sameFrame installed hdeeper
        frame member owner
      simp [Exec.descendantFrames] at member
  case doneOk curPc s d spawned resume nextPc settled nextPre e hstep henter
      hresume next ih =>
      intro dp ca rootPc rootPre rootOut rootRun invocation sameFrame installed hdeeper
        frame member owner
      have hcode : d.getCode ca = nextPre.getCode ca := by
        symm
        exact step_ok_runtimeCode_eq (dp := dp) (ca := ca) (xl := .none)
          trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter,
            hresume.symm⟩) installed
      have installedNext : some (nextPre.getCode ca).toList =
          (runtime dp).compile := by
        rw [← hcode]
        exact installed
      let edge : Exec.Deriv.ParentStep
          ⟨nextPc, s, nextPre, e, next⟩
          ⟨curPc, s, d, e, Exec.doneOk hstep henter hresume next⟩ :=
        .doneOk hstep henter hresume next
      exact ih invocation (sameFrame.snoc edge) installedNext hdeeper frame
        (by simpa only [Exec.descendantFrames] using member) owner
  case runErr curPc s d spawned resume nextPc cevm raw e hstep henter child
      hresume ihChild =>
      intro dp ca rootPc rootPre rootOut rootRun invocation sameFrame installed hdeeper
        frame member owner
      simp [Exec.descendantFrames] at member
  case runOk curPc s d spawned resume nextPc cevm raw nextPre e hstep henter
      child hresume next ihChild ihNext =>
      intro dp ca rootPc rootPre rootOut rootRun invocation sameFrame installed hdeeper
        retained member owner
      obtain ⟨x, hxat, hs, hpc⟩ := Evm.step_spawn_inv hstep
      have direct :=
        Blanc.LidoCircuitBreaker.runtimeExec_instruction_exact
          invocation sameFrame hxat
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hsevmTarget : s.currentTarget = ca := invocation.2.1
      have hchildAt : Prog.At (runtime dp) ca
          cevm.pc cevm.sta cevm.dyna := by
        refine ⟨?_, fun htarget => ⟨?_, hpc0⟩⟩
        · rw [hgc ca]
          exact installed
        · have hinnerTarget : spawned.inner.currentTarget = ca := by
            rw [← Frame.enter_run_currentTarget henter]
            exact htarget
          have hsameTarget : spawned.inner.currentTarget =
              s.currentTarget := hinnerTarget.trans hsevmTarget.symm
          have hinnerCode := directExternalStep_sameTarget_code direct hs
            hsameTarget (by rw [hinnerTarget]
                            exact not_delegation_of_compile installed)
          rw [Frame.enter_run_code henter, hinnerCode, hinnerTarget]
          exact installed
      have hchildDirect : cevm.sta.currentTarget = ca →
          cevm.sta.codeAddress = some ca := by
        intro htarget
        have hinnerTarget : spawned.inner.currentTarget = ca := by
          rw [← Frame.enter_run_currentTarget henter]
          exact htarget
        have hcadr := directExternalStep_codeAddress direct hs
        rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
        have hcadrInit := congrArg (fun e : Evm => e.sta.codeAddress) hinit
        dsimp [initEvm, initSevm, Msg.withBenv] at hcadrInit
        rw [hcadrInit, hcadr, hinnerTarget]
      have hdepth : cevm.sta.depth < s.depth := by
        rw [Frame.enter_run_depth henter]
        exact Step.spawn_depth_lt hstep
      have childClosed := hdeeper cevm.pc cevm.sta cevm.dyna raw
        child hdepth hchildAt
      have hchildRel : Xlot.Rel Devm.CodePreserve
          (.some ⟨cevm, raw⟩) :=
        Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
          Ninst.codePreserve_effectRec Jinst.codePreserve_effect
          Linst.codePreserve_effect child
      have installedNext : some (nextPre.getCode ca).toList =
          (runtime dp).compile := by
        rw [step_ok_runtimeCode_eq (dp := dp) (ca := ca) hchildRel
          (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
          installed]
        exact installed
      let edge : Exec.Deriv.ParentStep
          ⟨nextPc, s, nextPre, e, next⟩
          ⟨curPc, s, d, e,
            Exec.runOk hstep henter child hresume next⟩ :=
        .runOk hstep henter child hresume next
      have nextClosed := ihNext invocation (sameFrame.snoc edge) installedNext hdeeper
      by_cases childSettles : Frame.settlementCommits spawned raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits
          hstep henter child hresume next childSettles] at member
        simp only [List.mem_cons, List.mem_append] at member
        have childCommits := Frame.raw_commits_of_settlementCommits childSettles
        rcases member with (rfl | childMember) | nextMember
        · exact childClosed child childCommits hchildAt hchildDirect
            (Exec.Frame.ofRun child childCommits)
            (by unfold Exec.committedFrames
                rw [dif_pos childCommits]
                simp) owner
        · exact childClosed child childCommits hchildAt hchildDirect retained
            (by unfold Exec.committedFrames
                rw [dif_pos childCommits]
                simp [childMember]) owner
        · exact nextClosed retained nextMember owner
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits
          hstep henter child hresume next childSettles] at member
        exact nextClosed retained member owner

/-- Exact installed runtime bodies close owner identity for their committed
root and every settlement-retained descendant. -/
private theorem Exec.CoreRuntimeOwnerClosed.atTarget
    {dp : DeployParams} {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (_programRun : Prog.Run sevm pre (runtime dp) post)
    (target : sevm.currentTarget = ca)
    (hdeeper : ForallDeeperAt sevm.depth ca (runtime dp)
      (fun pc s d e _ => Exec.CoreRuntimeOwnerClosed dp ca pc s d e)) :
    Exec.CoreRuntimeOwnerClosed dp ca 0 sevm pre (.ok post) := by
  intro run committed installed direct frame member owner
  let root : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  have rootExact : root.exactInvocation (runtime dp) ca ca := by
    refine ⟨rfl, target, direct target, ?_⟩
    exact (installed.2 target).1
  unfold Exec.committedFrames at member
  rw [dif_pos committed] at member
  simp only [List.mem_cons] at member
  rcases member with rfl | descendant
  · simpa only [root, Exec.Frame.exactInvocation_iff_rootDeriv,
      Exec.Frame.rootDeriv, Exec.Frame.ofRun] using rootExact
  · exact Exec.runtimeDescendantOwnerClosure run rootExact (.refl root)
      installed.1 hdeeper frame descendant owner

/-- The generic depth recursion instantiated with the exact Lido runtime's
reviewed direct external-edge boundary. -/
theorem Exec.coreRuntimeOwnerClosed
    {dp : DeployParams} {ca : Adr} :
    Exec.Fa (Exec.Wkn ca (runtime dp)
      (fun pc sevm pre out _ =>
        Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreRuntimeOwnerClosed dp ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreRuntimeOwnerClosed dp ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := runtime dp)
  · intro sevm pre post programRun target hdeeper
    exact Exec.CoreRuntimeOwnerClosed.atTarget programRun target hdeeper
  · intro pc sevm devm err devm' target
    exact Exec.CoreRuntimeOwnerClosed.error
  · intro pc sevm devm hnone foreign
    exact Exec.CoreRuntimeOwnerClosed.error
  · intro pc sevm devm n err devm' hat hstep foreign
    exact Exec.CoreRuntimeOwnerClosed.error
  · intro pc sevm devm n cevm raw err devm' hat hstep child foreign ihChild
    exact Exec.CoreRuntimeOwnerClosed.error
  · intro pc sevm devm n devm' out hat hstep next foreign ihNext
    exact Exec.CoreRuntimeOwnerClosed.nextNone
      hat hstep next foreign ihNext
  · intro pc sevm devm n cevm raw devm' out hat hstep child next foreign
      ihChild ihNext
    exact Exec.CoreRuntimeOwnerClosed.nextSome
      hat hstep child next foreign ihChild ihNext
  · intro pc sevm devm j err devm' hat hstep foreign
    exact Exec.CoreRuntimeOwnerClosed.error
  · intro pc sevm devm j pc' devm' out hat hstep next foreign ihNext
    exact Exec.CoreRuntimeOwnerClosed.jump hat hstep next foreign ihNext
  · intro pc sevm devm l out hat hstep foreign
    exact Exec.CoreRuntimeOwnerClosed.last hat hstep foreign

/-- Public committed-frame closure for a global execution rooted at the exact
installed Lido runtime. -/
theorem Exec.runtimeOwnerClosure
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (installed : Prog.At (runtime dp) ca pc sevm pre)
    (rootExact :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca) :
    ∀ frame ∈ Exec.committedFrames run,
      frame.sevm.currentTarget = ca →
        frame.exactInvocation (runtime dp) ca ca := by
  have lifted := Exec.coreRuntimeOwnerClosed (dp := dp) (ca := ca)
    pc sevm pre out run installed
  exact lifted run committed installed
    (fun target => by simpa only [target] using rootExact.2.2.1)

/-- Same-frame prefixes preserve the static execution environment. -/
private theorem parentPrefix_sevm_eq
    {root target : Exec.Deriv}
    (sameFrame : Exec.Deriv.ParentPrefix root target) :
    root.sevm = target.sevm := by
  induction sameFrame with
  | refl => rfl
  | step head rest ih =>
      cases head <;> exact ih

/-- A retained successful SSTORE owned by the CircuitBreaker account belongs
to a committed exact runtime frame whose same-frame prefix reaches the write.
No chosen-writer identity premise is assumed. -/
theorem Exec.retainedSstore_runtimeOwnerClosure
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (installed : Prog.At (runtime dp) ca pc sevm pre)
    (rootExact :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca)
    (write : Exec.SuccessfulSstoreOccurrence
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
    (retained : write.Retained)
    (owner : write.storageOwner = ca) :
    ∃ frame ∈ Exec.committedFrames run,
      frame.exactInvocation (runtime dp) ca ca ∧
        Exec.Deriv.ParentPrefix frame.rootDeriv write.occurrence.node := by
  rcases (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
      run write.occurrence.node).mp retained with
    ⟨frame, member, sameFrame⟩
  have targetEq : frame.sevm.currentTarget =
      write.occurrence.node.sevm.currentTarget := by
    exact congrArg Sevm.currentTarget (parentPrefix_sevm_eq sameFrame)
  refine ⟨frame, member, ?_, sameFrame⟩
  exact Exec.runtimeOwnerClosure run committed installed rootExact frame member
    (targetEq.trans (by
      simpa only [Exec.SuccessfulSstoreOccurrence.storageOwner] using owner))

end Blanc.LidoCircuitBreaker
