import Blanc.Composition.Weth9TokenFramesNode
import Blanc.Lift.Weth9.FootHistory
import Blanc.ExecutionAccountingPositional
import Blanc.ExecutionCallerExclusion
import Blanc.ExecutionDirectCode
import Blanc.ExecIdentification
import Blanc.ExecDeterminism
import Blanc.Lift.RetainedTargetCompleteness

/-!
# Every committed frame below a WETH9-admitted run: precondition, code and code address

Fix a tracked universe `U` with injective slots.  `FrameOk ca U f` is what the token core needs at a
committed frame `f`: the footprint precondition at its entry (`(footSpec U).PreWf`, so the booked
total fits a word there), WETH9's code bookkeeping (`weth9Sem.At`: the code installed at `ca`, and a
frame at `ca` runs the WETH9 bytes from pc `0`, static frames included), the code address of a frame
at `ca` (`some ca`), and a covered fork.

`weth9_framesOk` proves, for every derivation entered in those facts and admitted at `ca`, that every
committed descendant frame satisfies `FrameOk`.  It is a depth induction through `lift_core_sem`:

* at a foreign node the precondition moves along same-frame steps (`Ninst.none_preserves_precond`), into
  a spawned child and back after it (`Xinst.some_preserves_precond`, with the child's postcondition from
  WETH9's frame theorem `footSpec_preservesAdmitted`); a child at `ca` is a direct `CALL`/`STATICCALL`
  child (`Xinst.step_spawn_codeAddress_eq_currentTarget`: `CALLCODE`/`DELEGATECALL` keep the foreign
  target, `CREATE` cannot land on code);
* a WETH9 frame's only external node is `withdraw`'s `CALL` (`weth9_exec_node`), after which it spawns
  nothing; its child starts in the precondition (`withdraw_child_pre`), at its callee's own code
  address (WETH9's code is no delegation designator).
-/

namespace Blanc.Composition.Weth9TokenFrames

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.ExecutionTrace

/-- What every committed frame carries. -/
structure FrameOk (ca : Adr) (U : Key → Prop) (f : Exec.Frame) : Prop where
  pre : (footSpec U).PreWf ca f.sevm f.pre
  at_ : weth9Sem.At ca f.pc f.sevm f.pre
  codeAddress : f.sevm.currentTarget = ca → f.sevm.codeAddress = some ca
  fork : CoveredFork f.sevm.benvStat.fork

/-- The induction motive: a committed derivation entered in the frame facts and admitted at `ca`
has only `FrameOk` descendants. -/
def FramesOk (ca : Adr) (U : Key → Prop) (pc : Nat) (sevm : Sevm) (pre : Devm)
    (out : Execution) : Prop :=
  ∀ run : Exec pc sevm pre out, Execution.commits out = true →
    CoveredFork sevm.benvStat.fork → weth9Sem.At ca pc sevm pre →
    Exec.FrameAdmitted ca (footEntry U) run → (footSpec U).PreWf ca sevm pre →
    (sevm.currentTarget = ca → sevm.codeAddress = some ca) →
    ∀ f ∈ Exec.descendantFrames run, FrameOk ca U f

/-- WETH9's code is no delegation designator. -/
theorem nodel_of_image {c : ByteArray} (h : some c.toList = weth9Sem.image) :
    getDelegatedCodeAddress c = none := by
  unfold getDelegatedCodeAddress
  simp only [weth9Sem.not_delegation h, ↓reduceIte]

/-- An entered frame's memory is well formed. -/
theorem enter_wf {f : Frame} {cevm : Evm} (enter : f.enter = .run cevm) :
    Mem.Wf cevm.dyna.memory := by
  rw [Frame.enter_run_memory enter]
  exact Mem.wf_empty

section Handlers

variable {ca : Adr} {U : Key → Prop}

theorem FramesOk.error {pc : Nat} {sevm : Sevm} {pre : Devm} {e : EvmError × Devm} :
    FramesOk ca U pc sevm pre (.error e) := by
  intro _ committed
  simp only [Execution.commits, Bool.false_eq_true] at committed

theorem FramesOk.nextNone {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {out : Execution} (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out) (targetNe : sevm.currentTarget ≠ ca)
    (ih : FramesOk ca U (pc + n.size) sevm inter out) :
    FramesOk ca U pc sevm pre out := by
  intro run committed hfork installed admitted hpre _ f hf
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    rw [Exec.descendantFrames_eq_of_nextNone hat step run next] at hf
    have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
      (weth9Sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
    have codeEq := lift_core_sem.stepCode (xl := .none) trivial
      (by rw [Evm.step_next hat]; exact step) ca codeNe
    have interAt : weth9Sem.At ca (pc + n.size) sevm inter :=
      ⟨by rw [codeEq]; exact installed.1, fun target => (targetNe target).elim⟩
    have interAdmitted := admitted.of_descendants_of_ne targetNe
      (Exec.rawFrameDescendants_sub_of_stepNone hat step next run)
    have interPre : (footSpec U).Pre ca sevm inter :=
      ContractSpecSem.Ninst.none_preserves_precond hfork step targetNe hpre.pre
    exact ih next committed hfork interAt interAdmitted
      ⟨interPre, fun target => (targetNe target).elim⟩ (fun target => (targetNe target).elim) f hf

theorem FramesOk.jump {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {j : Jinst}
    {out : Execution} (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out) (targetNe : sevm.currentTarget ≠ ca)
    (ih : FramesOk ca U pc' sevm inter out) :
    FramesOk ca U pc sevm pre out := by
  intro run committed hfork installed admitted hpre _ f hf
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    rw [Exec.descendantFrames_eq_of_jump hat step run next] at hf
    have stateEq := Jinst.preserves_state step
    have interAt : weth9Sem.At ca pc' sevm inter :=
      ⟨by simpa only [Devm.getCode, Devm.getAcct, stateEq] using installed.1,
        fun target => (targetNe target).elim⟩
    have interAdmitted := admitted.of_descendants_of_ne targetNe
      (Exec.rawFrameDescendants_sub_of_jump hat step next run)
    have interPre : (footSpec U).Pre ca sevm inter :=
      ContractSpecSem.Pre.state_eq hpre.pre stateEq
    exact ih next committed hfork interAt interAdmitted
      ⟨interPre, fun target => (targetNe target).elim⟩ (fun target => (targetNe target).elim) f hf

theorem FramesOk.last {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l) : FramesOk ca U pc sevm pre out := by
  intro run _ _ _ _ _ _ f hf
  rw [Exec.descendantFrames_eq_nil_of_last hat run] at hf
  cases hf

/-- A filled step at an external instruction is one spawn of the driver whose child entered the
slot's machine and whose resumption reached the step's result. -/
theorem spawnOfStepRun {pc : Nat} {sevm : Sevm} {pre inter : Devm} {x : Xinst}
    {cevm : Evm} {raw : Execution}
    (hat : Ninst.At sevm.code pc (.exec x))
    (step : Ninst.StepRun pc sevm pre (.exec x) (.some ⟨cevm, raw⟩) (.ok inter)) :
    ∃ (frame : Jaune.Frame) (resume : Resume),
      Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume (pc + 1) ∧ frame.enter = .run cevm ∧
        resume.run (frame.settle raw) = .ok inter ∧ Xinst.step sevm pre x = .spawn frame resume := by
  have hxrun := XStep.run_toStep.mp step
  cases spawnEq : Xinst.step sevm pre x with
  | done execution => simp only [XStep.Run, spawnEq, ExceptT.stM_eq, reduceCtorEq,
    false_and] at hxrun
  | spawn frame resume =>
    simp only [spawnEq, XStep.Run] at hxrun
    obtain ⟨result, frameRun, resumeRun⟩ := hxrun
    obtain ⟨enter, settle⟩ := RunFrame.some_inv frameRun
    refine ⟨frame, resume, ?_, enter, ?_, rfl⟩
    · rw [Evm.step_next hat]
      simp only [Ninst.step_exec, spawnEq, XStep.toStep]
    · rw [← settle]
      exact resumeRun.symm

/-- **Foreign spawn.**  The child starts in the precondition (the parent's, moved by the spawn), at
`ca`'s code if it targets `ca` (a direct call child, at its own code address); after it, the
continuation is in the precondition again (the child's postcondition, from WETH9's frame theorem). -/
theorem FramesOk.nextSome (hinj : KeyInj U) {pc : Nat} {sevm : Sevm} {pre inter : Devm}
    {n : Ninst} {cevm : Evm} {raw out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out) (targetNe : sevm.currentTarget ≠ ca)
    (ihChild : FramesOk ca U cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : FramesOk ca U (pc + n.size) sevm inter out) :
    FramesOk ca U pc sevm pre out := by
  cases n with
  | reg r => cases (Step.run_ofExecution.mp step).1
  | push xs length => cases (Step.run_ofExecution.mp step).1
  | dupn imm => cases (Step.run_ofExecution.mp step).1
  | swapn imm => cases (Step.run_ofExecution.mp step).1
  | exchange imm => cases (Step.run_ofExecution.mp step).1
  | exec x =>
  intro run committed hfork installed admitted hpre _ f hf
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
  obtain ⟨frame, resume, hroot, enter, hres, spawnX⟩ := spawnOfStepRun hat step
  have subsets := Exec.rawFrameDescendants_sub_of_stepSome hat step child next run
  have runEq : run = Exec.runOk hroot enter child hres next := Exec.unique _ _
  subst runEq
  have hx : Xinst.Run sevm pre x (.some ⟨cevm, raw⟩) (.ok inter) := XStep.run_toStep.mp step
  obtain ⟨childPre, back⟩ :=
    ContractSpecSem.Xinst.some_preserves_precond hfork hx child targetNe hpre.pre
  have childWf := Xinst.some_child_wf hx
  have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
    (weth9Sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
  have codeNe' : pre.getCode ca ≠ .empty := fun empty => codeNe (by
    rw [empty]; simp only [ByteArray.toList_empty])
  obtain ⟨-, codeEq⟩ := Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode
    (.step (.runOk hroot enter child hres next) (.refl _))
  have interAt : weth9Sem.At ca (pc + 1) sevm inter :=
    ⟨by rw [codeEq ca codeNe]; exact installed.1, fun target => (targetNe target).elim⟩
  obtain ⟨pcZero, childCode, codeSource⟩ := Evm.step_spawn_child hroot enter
  have childAt : weth9Sem.At ca cevm.pc cevm.sta cevm.dyna := by
    refine ⟨by rw [childCode ca]; exact installed.1, fun childTarget => ⟨?_, pcZero⟩⟩
    rw [codeSource (by rw [childTarget]; exact targetNe) (by rw [childTarget]; exact codeNe')
      (by rw [childTarget]; exact weth9Sem.not_delegation installed.1), childTarget]
    exact installed.1
  have childFork := Evm.step_spawn_child_fork hroot enter hfork
  have childAdmitted : Exec.FrameAdmitted ca (footEntry U) child := admitted.mono fun root member =>
    List.mem_cons_of_mem _ (subsets.1 root member)
  have nextAdmitted := admitted.of_descendants_of_ne targetNe subsets.2
  have childCodeAddress : cevm.sta.currentTarget = ca → cevm.sta.codeAddress = some ca := by
    intro childTarget
    have innerTarget : frame.inner.currentTarget = ca := by
      rw [← Frame.enter_run_currentTarget enter, childTarget]
    rw [Frame.enter_run_codeAddress enter,
      Xinst.step_spawn_codeAddress_eq_currentTarget spawnX (by rw [innerTarget]; exact targetNe)
        (by rw [innerTarget]; exact codeNe') (by rw [innerTarget]; exact nodel_of_image installed.1),
      innerTarget]
  have childPreWf : (footSpec U).PreWf ca cevm.sta cevm.dyna := ⟨childPre, fun _ => childWf⟩
  have childPost : ifOk ((footSpec U).Post ca cevm.sta) raw := by
    have key : ∀ {p : Nat} {childPost : Devm} (e : Exec p cevm.sta cevm.dyna (.ok childPost)),
        p = 0 → Exec.FrameAdmitted ca (footEntry U) e →
          (footSpec U).Post ca cevm.sta childPost := by
      intro p childPost e hp adm
      subst hp
      exact footSpec_preservesAdmitted ca hinj _ _ _ childFork e adm (fun t => (childAt.2 t).1)
        (fun _ => childWf) childPre
    cases raw with
    | error e => trivial
    | ok childPost => exact key child pcZero childAdmitted
  have interPreWf : (footSpec U).PreWf ca sevm inter :=
    ⟨back childPost, fun t => (targetNe t).elim⟩
  have noCA : sevm.currentTarget = ca → sevm.codeAddress = some ca := fun t => (targetNe t).elim
  by_cases settles : Frame.settlementCommits frame raw = true
  · have hraw := Frame.raw_commits_of_settlementCommits settles
    rw [Exec.descendantFrames_runOk_of_settlementCommits hroot enter child hres next settles] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨childPreWf, childAt, childCodeAddress, childFork⟩
    rcases List.mem_append.mp hf with hc | hn
    · exact ihChild child hraw childFork childAt childAdmitted childPreWf childCodeAddress f hc
    · exact ihNext next committed hfork interAt nextAdmitted interPreWf noCA f hn
  · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hroot enter child hres next
      settles] at hf
    exact ihNext next committed hfork interAt nextAdmitted interPreWf noCA f hf

/-- **WETH9 frame.**  Its only external node is `withdraw`'s `CALL`, after which it spawns nothing;
the child starts in the precondition, at WETH9's code if it re-enters, at its own code address. -/
theorem FramesOk.target (hinj : KeyInj U) {sevm : Sevm} {pre post : Devm}
    (hrun : weth9Sem.Run sevm pre post) (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca weth9Sem
      (fun pc s d e _ => FramesOk ca U pc s d e)) :
    FramesOk ca U 0 sevm pre (.ok post) := by
  subst target
  intro run _ fork installed admitted hpre _ f hf
  have hcode : sevm.code = code := hrun.1
  have hkeys : ∀ k ∈ frameKeys sevm, U k := admitted.root rfl
  have hcaller : U (.bal sevm.caller) := hkeys _ List.mem_cons_self
  rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
  · rw [Exec.descendantFrames_eq_nil_of_noExec run none] at hf
    cases hf
  have hpV := hV.parentPrefix
  have dEq := hV.descendantFrames_eq
  obtain ⟨x, hx⟩ := hV.exec_at
  have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
  obtain ⟨-, hle, hstor, hafter⟩ := weth9_exec_node run hcode fork hpV ⟨x, hx⟩
  obtain ⟨hcall, hbal, gw, cw, ys, hstk⟩ := weth9_exec_node_call run hcode fork hpV ⟨x, hx⟩
  have sevmEq : Vn.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV
  have codeNe : (pre.getCode sevm.currentTarget).toList ≠ [] := fun empty =>
    weth9Sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have nodeCode : Vn.devm.getCode sevm.currentTarget = pre.getCode sevm.currentTarget :=
    (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).2 _ codeNe
  obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
  dsimp only at hexn hx dEq sevmEq hstor hbal hstk hcall nodeCode hafter hpV
  subst hexn sevmEq
  rw [dEq] at hf
  cases vrun with
  | halt step =>
      rw [Evm.step_next hx] at step
      exact (Ninst.step_ne_halt_ok step).elim
  | cont step next =>
      have hdf := Exec.descendantFrames_eq_nil_of_noExec next (hafter _ (.cont step next)).2
      simp only [Exec.descendantFrames, hdf, List.not_mem_nil] at hf
  | doneOk step enter resume next =>
      have hdf := Exec.descendantFrames_eq_nil_of_noExec next
        (hafter _ (.doneOk step enter resume next)).2
      simp only [Exec.descendantFrames, hdf, List.not_mem_nil] at hf
  | runOk step enter child resume next =>
      rename_i frame rsm pc' cevm raw inter
      have hdf := Exec.descendantFrames_eq_nil_of_noExec next
        (hafter _ (.runOk step enter child resume next)).2
      have spawnCall : Xinst.step vsevm vd .call = .spawn frame rsm := by
        have h := step
        rw [Evm.step_next hcall] at h
        exact XStep.toStep_spawn (by simpa only [Ninst.step_exec] using h)
      obtain ⟨pcZero, childCode, -⟩ := Evm.step_spawn_child step enter
      have childPre := withdraw_child_pre hinj rfl fork hcaller hpre.pre hle hstor hbal nodeCode
        hcall hstk step enter
      have childAt : weth9Sem.At vsevm.currentTarget cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [childCode, nodeCode]; exact installed.1, fun childTarget => ⟨?_, pcZero⟩⟩
        have sameTarget : frame.inner.currentTarget = vsevm.currentTarget := by
          rw [← Frame.enter_run_currentTarget enter, childTarget]
        have notDel : ¬ isValidDelegation (vd.getCode frame.inner.currentTarget) := by
          rw [sameTarget, nodeCode]
          exact weth9Sem.not_delegation installed.1
        rw [Frame.enter_run_code enter, Xinst.step_call_sameTarget_code spawnCall sameTarget notDel,
          sameTarget, nodeCode]
        exact installed.1
      have childCodeAddress : cevm.sta.currentTarget = vsevm.currentTarget →
          cevm.sta.codeAddress = some vsevm.currentTarget := by
        intro childTarget
        have sameTarget : frame.inner.currentTarget = vsevm.currentTarget := by
          rw [← Frame.enter_run_currentTarget enter, childTarget]
        rw [Frame.enter_run_codeAddress enter, Xinst.step_callKind_spawn_codeAddress (Or.inl rfl)
          spawnCall (by rw [sameTarget, nodeCode]; exact nodel_of_image installed.1), sameTarget]
      have childFork := Evm.step_spawn_child_fork step enter fork
      have childDepth : cevm.sta.depth < vsevm.depth := by
        rw [Frame.enter_run_depth enter]
        exact Step.spawn_depth_lt step
      have childAdmitted : Exec.FrameAdmitted vsevm.currentTarget (footEntry U) child := by
        intro childRoot member selected
        refine admitted childRoot (List.mem_cons_of_mem _
          (Exec.mem_rawFrameDescendants_of_parentPrefix hpV ?_)) selected
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
        rcases member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr (Or.inl member)
      have childPreWf : (footSpec U).PreWf vsevm.currentTarget cevm.sta cevm.dyna :=
        ⟨childPre, fun _ => enter_wf enter⟩
      by_cases settles : Frame.settlementCommits frame raw = true
      · have hraw := Frame.raw_commits_of_settlementCommits settles
        rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next settles,
          hdf, List.append_nil] at hf
        rcases List.mem_cons.mp hf with rfl | hd
        · exact ⟨childPreWf, childAt, childCodeAddress, childFork⟩
        · exact deeper _ _ _ _ child childDepth childAt child hraw childFork childAt childAdmitted
            childPreWf childCodeAddress f hd
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next
          settles, hdf] at hf
        cases hf

end Handlers

/-- **Every committed descendant of a WETH9-admitted derivation carries the frame facts.** -/
theorem weth9_framesOk (ca : Adr) {U : Key → Prop} (hinj : KeyInj U) :
    Exec.Fa (Exec.WknSem ca weth9Sem (fun pc s d e _ => FramesOk ca U pc s d e)) :=
  lift_core_sem (fun pc s d e => FramesOk ca U pc s d e) (fun s d p => FramesOk ca U 0 s d (.ok p))
    (fun h => h) ca weth9Sem
    (fun hrun target deeper => FramesOk.target hinj hrun target deeper)
    (fun _ => FramesOk.error)
    (fun _ _ => FramesOk.error)
    (fun _ _ _ => FramesOk.error)
    (fun _ _ _ _ _ => FramesOk.error)
    (fun hat step next targetNe ih => FramesOk.nextNone hat step next targetNe ih)
    (fun hat step child next targetNe ihChild ihNext =>
      FramesOk.nextSome hinj hat step child next targetNe ihChild ihNext)
    (fun _ _ _ => FramesOk.error)
    (fun hat step next targetNe ih => FramesOk.jump hat step next targetNe ih)
    (fun hat _ _ => FramesOk.last hat)

end Blanc.Composition.Weth9TokenFrames
