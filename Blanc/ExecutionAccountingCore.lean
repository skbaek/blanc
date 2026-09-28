import Blanc.ExecutionAccountingObserved
import Blanc.ExecutionAdmissionSem
import Blanc.ExecIdentification
import Blanc.ExecutionTraceFrames

/-!
# Observed accounting for admitted concrete execution

The target supplies its semantic frame handler. Foreign instructions compose
the account-local replay through actual child settlement and retain exactly
the committed-frame observation. Static observation emptiness is independent
of the balance bound needed by the accounting transport.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- A committed concrete run has no observed static actions and, under the
world word bound, an exact observed accounting replay. Admission is attached
to the supplied derivation, including its actually entered child roots. -/
def Exec.CoreAccounting (ca : Adr) (sem : CodeSem)
    (entry : Sevm → Devm → Prop) (C : ReplayCarrier ca) (V : ReplayObservation C)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out) (committed : Execution.commits out = true),
    CoveredFork sevm.benvStat.fork → sem.At ca pc sevm pre →
    Exec.FrameAdmitted ca entry run →
    (sevm.isStatic = true → (Exec.committedFrames run).flatMap V.frameObs = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs)

namespace Exec.CoreAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop}
    {C : ReplayCarrier ca} {V : ReplayObservation C}

private def boundSpec (sem : CodeSem) : ContractSpecSem where
  sem := sem
  Inv := fun _ _ _ => True
  Side := fun balances => sum balances < 2 ^ 256
  inv_forget := fun _ => trivial
  inv_mono := fun _ _ => trivial
  inv_recv := fun _ _ => trivial
  side_le := fun bound le => Nat.lt_of_le_of_lt le bound
  side_transfer := by
    intro st st' caller callee wad sub bound
    rw [of_state_transfer_sum sub bound]
    exact bound
  side_addBal := by
    intro st target value bound _
    rw [sum_addBal_eq st target value bound]
    exact bound
  inv_transfer := fun _ _ _ _ => trivial
  inv_recv_transfer := fun _ _ _ _ => trivial
  inv_addBal := fun _ _ _ => trivial

private theorem foreign_observation
    (obsForeign : ∀ frame : Exec.Frame,
      frame.sevm.currentTarget ≠ ca → V.frameObs frame = [])
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (targetNe : sevm.currentTarget ≠ ca) :
    (Exec.committedFrames run).flatMap V.frameObs =
      (Exec.descendantFrames run).flatMap V.frameObs := by
  rw [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons,
    obsForeign _ targetNe, List.nil_append]

theorem error {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreAccounting ca sem entry C V pc sevm pre (.error error) := by
  intro _ committed
  simp [Execution.commits] at committed

theorem nextNone
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c →
      C.Replay a (xs ++ ys) c)
    (tag : Sevm → Devm → C.Tag)
    (entryForeign : ∀ sevm state, sevm.currentTarget ≠ ca →
      C.frameEntry sevm state = C.ofState state)
    (obsForeign : ∀ frame : Exec.Frame,
      frame.sevm.currentTarget ≠ ca → V.frameObs frame = [])
    {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (targetNe : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreAccounting ca sem entry C V (pc + n.size) sevm inter out) :
    Exec.CoreAccounting ca sem entry C V pc sevm pre out := by
  intro run committed hfork installed admitted
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
    have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
      (sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
    have codeEq := lift_core_sem.stepCode (xl := .none) trivial
      (by rw [Evm.step_next hat]; exact step) ca codeNe
    have interAt : sem.At ca (pc + n.size) sevm inter :=
      ⟨by rw [codeEq]; exact installed.1, fun target => (targetNe target).elim⟩
    have interAdmitted := admitted.of_descendants_of_ne targetNe
      (Exec.rawFrameDescendants_sub_of_stepNone hat step next run)
    obtain ⟨staticTail, replayTail⟩ := ih next committed hfork interAt interAdmitted
    have observations : (Exec.committedFrames run).flatMap V.frameObs =
        (Exec.committedFrames next).flatMap V.frameObs := by
      rw [foreign_observation obsForeign run committed targetNe,
        foreign_observation obsForeign next committed targetNe,
        Exec.descendantFrames_eq_of_nextNone hat step run next]
    refine ⟨fun static => observations.trans (staticTail static), ?_⟩
    intro bound
    have interBound : sum inter.state.bal < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Ninst.balance_effectRec n (xl := .none) trivial step) bound
    obtain ⟨heads, headReplay, headObs⟩ :=
      C.ofStorageEqBalanceMono_observed V (tag sevm pre)
        (Ninst.foreignNone_getStor_eq hfork step targetNe)
        (Ninst.targetBalanceMono_of_none hfork step targetNe bound)
    obtain ⟨tails, tailReplay, tailObs⟩ := replayTail interBound
    rw [entryForeign _ _ targetNe] at tailReplay ⊢
    refine ⟨heads ++ tails, append headReplay tailReplay, ?_⟩
    rw [V.obs_append, headObs, List.nil_append, tailObs, observations]

theorem jump
    (entryForeign : ∀ sevm state, sevm.currentTarget ≠ ca →
      C.frameEntry sevm state = C.ofState state)
    (obsForeign : ∀ frame : Exec.Frame,
      frame.sevm.currentTarget ≠ ca → V.frameObs frame = [])
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {j : Jinst} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out) (targetNe : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreAccounting ca sem entry C V pc' sevm inter out) :
    Exec.CoreAccounting ca sem entry C V pc sevm pre out := by
  intro run committed hfork installed admitted
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
    have stateEq := Jinst.preserves_state step
    have interAt : sem.At ca pc' sevm inter :=
      ⟨by simpa only [Devm.getCode, Devm.getAcct, stateEq] using installed.1,
        fun target => (targetNe target).elim⟩
    have interAdmitted := admitted.of_descendants_of_ne targetNe
      (Exec.rawFrameDescendants_sub_of_jump hat step next run)
    obtain ⟨staticTail, replayTail⟩ := ih next committed hfork interAt interAdmitted
    have observations : (Exec.committedFrames run).flatMap V.frameObs =
        (Exec.committedFrames next).flatMap V.frameObs := by
      rw [foreign_observation obsForeign run committed targetNe,
        foreign_observation obsForeign next committed targetNe,
        Exec.descendantFrames_eq_of_jump hat step run next]
    refine ⟨fun static => observations.trans (staticTail static), ?_⟩
    intro bound
    obtain ⟨steps, replay, observed⟩ := replayTail (by simpa only [stateEq] using bound)
    rw [entryForeign _ _ targetNe, stateEq] at replay
    rw [entryForeign _ _ targetNe]
    exact ⟨steps, replay, observed.trans observations.symm⟩

theorem last
    (tag : Sevm → Devm → C.Tag)
    (entryForeign : ∀ sevm state, sevm.currentTarget ≠ ca →
      C.frameEntry sevm state = C.ofState state)
    (obsForeign : ∀ frame : Exec.Frame,
      frame.sevm.currentTarget ≠ ca → V.frameObs frame = [])
    {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l) (step : Linst.Run sevm pre l out)
    (targetNe : sevm.currentTarget ≠ ca) :
    Exec.CoreAccounting ca sem entry C V pc sevm pre out := by
  intro run committed _ _ _
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
    have observations : (Exec.committedFrames run).flatMap V.frameObs = [] := by
      rw [foreign_observation obsForeign run committed targetNe,
        Exec.descendantFrames_eq_nil_of_last hat run, List.flatMap_nil]
    refine ⟨fun _ => observations, ?_⟩
    intro bound
    obtain ⟨steps, replay, observed⟩ :=
      C.ofStorageEqBalanceMono_observed V (tag sevm pre)
        (congrFun (Linst.getStor_eq step) ca)
        (Linst.targetBalanceMono_of_foreign step targetNe bound)
    rw [entryForeign _ _ targetNe]
    exact ⟨steps, replay, observed.trans observations.symm⟩

private theorem foreignSpawn
    {pc : Nat} {sevm : Sevm} {pre inter : Devm} {x : Xinst}
    {cevm : Evm} {raw : Execution}
    (hat : Ninst.At sevm.code pc (.exec x))
    (step : Ninst.StepRun pc sevm pre (.exec x) (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (targetNe : sevm.currentTarget ≠ ca) (installed : sem.At ca pc sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∃ (frame : Jaune.Frame) (resume : Resume) (settled : Devm),
      Xinst.step sevm pre x = .spawn frame resume ∧
      RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled) ∧
      resume.run (.ok settled) = .ok inter ∧
      sem.At ca cevm.pc cevm.sta cevm.dyna ∧
      sem.At ca (pc + 1) sevm inter ∧ CoveredFork cevm.sta.benvStat.fork := by
  have xrun : Xinst.Run sevm pre x (.some ⟨cevm, raw⟩) (.ok inter) :=
    XStep.run_toStep.mp step
  have hxrun := XStep.run_toStep.mp step
  cases spawnEq : Xinst.step sevm pre x with
  | done execution => simp [spawnEq, XStep.Run] at hxrun
  | spawn frame resume =>
    simp only [spawnEq, XStep.Run] at hxrun
    obtain ⟨result, frameRun, resumeRun⟩ := hxrun
    cases result with
    | error error =>
      cases resume <;> simp [Resume.run, liftToExecution] at resumeRun
    | ok settled =>
      have enter := (RunFrame.some_inv frameRun).1
      have evmStep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume (pc + 1) := by
        rw [Evm.step_next hat]
        simp only [Ninst.step_exec, spawnEq, XStep.toStep]
      obtain ⟨childPcZero, childGetCode, childCodeSource⟩ :=
        Evm.step_spawn_child evmStep enter
      have childAt : sem.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [childGetCode ca]; exact installed.1,
          fun childTarget => ⟨?_, childPcZero⟩⟩
        have targetsNe : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [childTarget]
          exact targetNe
        have codeEq := childCodeSource targetsNe
          (by rw [childTarget]; exact not_empty_of_codeSem installed.1)
          (by rw [childTarget]; exact sem.not_delegation installed.1)
        rw [codeEq, childTarget]
        exact installed.1
      have childCode : Xlot.Rel Devm.CodePreserve (.some ⟨cevm, raw⟩) :=
        Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
          Ninst.codePreserve_effectRec Jinst.codePreserve_effect
          Linst.codePreserve_effect child
      have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
        (sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
      have codeEq := lift_core_sem.stepCode childCode
        (by rw [Evm.step_next hat]; exact step) ca codeNe
      have interAt : sem.At ca (pc + 1) sevm inter :=
        ⟨by rw [codeEq]; exact installed.1, fun target => (targetNe target).elim⟩
      exact ⟨frame, resume, settled, rfl, frameRun, resumeRun.symm,
        childAt, interAt, Xinst.Run.some_child_fork xrun hfork⟩

theorem nextSome
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c →
      C.Replay a (xs ++ ys) c)
    (entryForeign : ∀ sevm state, sevm.currentTarget ≠ ca →
      C.frameEntry sevm state = C.ofState state)
    (obsForeign : ∀ frame : Exec.Frame,
      frame.sevm.currentTarget ≠ ca → V.frameObs frame = [])
    {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {cevm : Evm} {raw out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (targetNe : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreAccounting ca sem entry C V cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreAccounting ca sem entry C V (pc + n.size) sevm inter out) :
    Exec.CoreAccounting ca sem entry C V pc sevm pre out := by
  cases n with
  | reg r =>
    cases (Step.run_ofExecution.mp step).1
  | push xs length =>
    cases (Step.run_ofExecution.mp step).1
  | dupn imm => cases (Step.run_ofExecution.mp step).1
  | swapn imm => cases (Step.run_ofExecution.mp step).1
  | exchange imm => cases (Step.run_ofExecution.mp step).1
  | exec x =>
    intro run committed hfork installed admitted
    cases out with
    | error error => simp [Execution.commits] at committed
    | ok post =>
      obtain ⟨frame, resume, settled, spawnEq, frameRun, resumeRun,
          childAt, interAt, childFork⟩ := foreignSpawn hat step child targetNe installed hfork
      obtain ⟨childSubset, nextSubset⟩ :=
        Exec.rawFrameDescendants_sub_of_stepSome hat step child next run
      have childAdmitted : Exec.FrameAdmitted ca entry child := admitted.mono (by
        intro root member
        exact List.mem_cons_of_mem _ (childSubset root member))
      have nextAdmitted := admitted.of_descendants_of_ne targetNe nextSubset
      have childAnswer := fun childCommitted =>
        ihChild child childCommitted childFork childAt childAdmitted
      obtain ⟨staticTail, replayTail⟩ := ihNext next committed hfork interAt nextAdmitted
      have observations : (Exec.committedFrames run).flatMap V.frameObs =
          (if Frame.settlementCommits frame raw = true
            then (Exec.committedFrames child).flatMap V.frameObs else []) ++
          (Exec.committedFrames next).flatMap V.frameObs := by
        rw [foreign_observation obsForeign run committed targetNe,
          foreign_observation obsForeign next committed targetNe]
        exact Exec.descendantFrames_flatMap_of_nextSome V.frameObs
          hat spawnEq frameRun resumeRun run child next
      refine ⟨?_, ?_⟩
      · intro static
        have childStatic : cevm.sta.isStatic = true :=
          (Frame.enter_run_isStatic (RunFrame.some_inv frameRun).1).trans
            (Xinst.step_spawn_isStatic spawnEq static)
        rw [observations, staticTail static, List.append_nil]
        split
        · rename_i settles
          exact (childAnswer (Frame.raw_commits_of_settlementCommits settles)).1 childStatic
        · rfl
      · intro bound
        have xrun : Xinst.Run sevm pre x (.some ⟨cevm, raw⟩) (.ok inter) :=
          XStep.run_toStep.mp step
        have opening : (boundSpec sem).Pre ca sevm pre :=
          ⟨installed.1, bound, fun _ => trivial, fun _ => trivial⟩
        obtain ⟨childPre, continuation⟩ :=
          ContractSpecSem.Xinst.some_preserves_precond hfork xrun child targetNe opening
        have childPost : ifOk ((boundSpec sem).Post ca cevm.sta) raw := by
          cases raw with
          | error error => trivial
          | ok childPost =>
            exact ⟨Nat.lt_of_le_of_lt (Exec.balance_effect child) childPre.side, trivial⟩
        have interBound : sum inter.state.bal < 2 ^ 256 := (continuation childPost).side
        obtain ⟨heads, headReplay, headObs⟩ :=
          C.xinstForeignSome_observed V spawnEq frameRun resumeRun targetNe
            hfork bound child (fun childCommitted => (childAnswer childCommitted).2 childPre.side)
        obtain ⟨tails, tailReplay, tailObs⟩ := replayTail interBound
        rw [entryForeign _ _ targetNe] at tailReplay ⊢
        refine ⟨heads ++ tails, append headReplay tailReplay, ?_⟩
        rw [V.obs_append, headObs, tailObs, observations]

/-- A retained message's actual transferred entry supplies semantic code
location and inherits the opening world's word bound. The message readiness
premise remains the existing independent contract-specification carrier. -/
theorem messageRoot_facts {c : ContractSpecSem} {msg : Msg} {entryBenv : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    (transfer : msg.benvAfterTransfer = .ok entryBenv)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entryBenv))
    (ready : c.MessageRunReady ca msg)
    (bound : sum msg.benv.state.bal < 2 ^ 256) :
    c.sem.At ca pc sevm pre ∧ sum pre.state.bal < 2 ^ 256 := by
  have precondition := ContractSpecSem.Pre.of_inv_benvAfterTransfer
    ready.ready.ne ready.ready.val0 transfer ready.ready.state
  have pcEq := congrArg Evm.pc evmEq
  have sevmEq := congrArg Evm.sta evmEq
  have preEq := congrArg Evm.dyna evmEq
  dsimp only [initEvm] at pcEq sevmEq preEq
  subst pc
  subst sevm
  subst pre
  refine ⟨⟨precondition.code, ?_⟩, ?_⟩
  · intro target
    refine ⟨?_, rfl⟩
    rcases ready.codeOrForeign with call | foreign
    · exact ready.ready.code call
        (by simpa [initSevm, Msg.withBenv] using target)
    · exact (foreign (by simpa [initSevm, Msg.withBenv] using target)).elim
  · change sum entryBenv.state.bal < 2 ^ 256
    have transferred := Msg.benvAfterTransfer_balance_effect
      (out := .ok entryBenv) transfer
    change sum entryBenv.state.bal ≤ sum msg.benv.state.bal at transferred
    exact Nat.lt_of_le_of_lt transferred bound

end Exec.CoreAccounting

/-- Lift a semantic target handler to every admitted concrete execution,
composing foreign child settlement and continuation observations in order. -/
theorem Exec.coreAccounting
    (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c →
      C.Replay a (xs ++ ys) c)
    (tag : Sevm → Devm → C.Tag)
    (entryForeign : ∀ sevm state, sevm.currentTarget ≠ ca →
      C.frameEntry sevm state = C.ofState state)
    (obsForeign : ∀ frame : Exec.Frame,
      frame.sevm.currentTarget ≠ ca → V.frameObs frame = [])
    (targetHandler : ∀ {sevm pre post}, sem.Run sevm pre post →
      sevm.currentTarget = ca →
      ForallDeeperAtSem sevm.depth ca sem
        (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e) →
      Exec.CoreAccounting ca sem entry C V 0 sevm pre (.ok post)) :
    Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)) := by
  apply lift_core_sem
    (ε := fun pc sevm pre out => Exec.CoreAccounting ca sem entry C V pc sevm pre out)
    (π := fun sevm pre post => Exec.CoreAccounting ca sem entry C V 0 sevm pre (.ok post))
    (analog := fun h => h) (ca := ca) (sem := sem)
  · exact targetHandler
  · intro pc sevm pre error post target
    exact Exec.CoreAccounting.error
  · intro pc sevm pre noneAt targetNe
    exact Exec.CoreAccounting.error
  · intro pc sevm pre n error post hat step targetNe
    exact Exec.CoreAccounting.error
  · intro pc sevm pre n childEvm childOut error post hat step child targetNe ihChild
    exact Exec.CoreAccounting.error
  · intro pc sevm pre n inter out hat step next targetNe ihNext
    exact Exec.CoreAccounting.nextNone append tag entryForeign obsForeign hat step next targetNe ihNext
  · intro pc sevm pre n childEvm childOut inter out hat step child next targetNe ihChild ihNext
    exact Exec.CoreAccounting.nextSome append entryForeign obsForeign hat step child next targetNe ihChild ihNext
  · intro pc sevm pre j error post hat step targetNe
    exact Exec.CoreAccounting.error
  · intro pc sevm pre j pc' inter out hat step next targetNe ihNext
    exact Exec.CoreAccounting.jump entryForeign obsForeign hat step next targetNe ihNext
  · intro pc sevm pre l out hat step targetNe
    exact Exec.CoreAccounting.last tag entryForeign obsForeign hat step targetNe

end Blanc
