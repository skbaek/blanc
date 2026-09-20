import Blanc.StaticStorage

/-!
# Representation-exact storage silence of static execution

`Blanc/StaticStorage.lean` proves that a successful `STATICCALL` preserves the
extensional storage observation `Devm.storageView`.  Consumers whose boundary
is the `Stor` tree itself — a replay carrier that meets at equal storages —
need the stronger statement: the storage map of every account is *equal*.

It holds, and for a simple reason.  Inside a static frame the only
instruction that writes persistent storage, `SSTORE`, cannot complete; every
other successful step, every message entry (`benvAfterTransfer`), every
successful settlement and every rollback moves the storage map only by an
equation already proved at `Stor` level.  `CREATE` never spawns from a static
frame.  This module packages that induction once, contract-neutrally, and
exposes it as the `Ninst.Hinv Devm.getStor Ninst.staticcall` instance that
`Func.SilentIn Devm.getStor` certificates consume.
-/

namespace Blanc

open Jaune

/-- One successful same-frame driver step of a static frame leaves every
storage map equal. -/
private theorem staticStep_cont_getStor
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (static : sevm.isStatic = true) :
    Devm.getStor post = Devm.getStor pre := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              have frame :=
                Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              exact (funext frame.getStor).symm
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction =
              .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size :=
            Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | push bytes bound =>
              exact (Ninst.Hinv.inv (f := Devm.getStor)
                (show Ninst.Run sevm pre (.push bytes bound) post from
                  ⟨.none, trivial, pc, nrun⟩)).symm
          | exec executable =>
              exact Xinst.none_getStor_eq (XStep.run_toStep.mp nrun)
          | reg regular =>
              by_cases store : regular = .sstore
              · subst regular
                have dynamic := of_run_sstore_not_static
                  (show Ninst.Run sevm pre Ninst.sstore post from
                    ⟨.none, trivial, pc, nrun⟩)
                rw [static] at dynamic
                exact Bool.noConfusion dynamic
              · have rrun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post := by
                  exact (Step.run_ofExecution.mp nrun).2.symm
                exact (Rinst.preserves_stor store rrun).symm

/-- A committing halted node ends in a successful last instruction, which
leaves every storage map equal. -/
private theorem staticHalt_getStor
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (committed : Execution.commits out = true) :
    Devm.getStor (Execution.committedPost out committed) =
      Devm.getStor pre := by
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
      cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
      | none =>
          unfold Evm.step at step
          rw [decoded] at step
          cases step
      | some instruction =>
          cases instruction with
          | next next =>
              rw [Evm.step_next decoded] at step
              exact (Ninst.step_ne_halt_ok step).elim
          | jump jumpInst =>
              rw [Evm.step_jump decoded] at step
              cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst <;>
                rw [jumpEq] at step <;> cases step
          | last last =>
              rw [Evm.step_last decoded] at step
              exact Linst.getStor_eq (Step.halt.inj step)

/-- A concrete CALL-family message whose body leaves every storage map equal
on commit settles with every storage map equal to its parent's: on commit
through the entry transfer and the committed body, on failure through the
rollback. -/
private theorem processMessage_getStor_of_body
    {msg : Msg} {post parent : Devm}
    {cevm : Evm} {out : Execution}
    (process : ProcessMessage msg (.some ⟨cevm, out⟩) (.ok post))
    (parentState : parent.state = msg.benv.state)
    (body : ∀ committed : Execution.commits out = true,
      Devm.getStor (Execution.committedPost out committed) =
        Devm.getStor cevm.dyna) :
    Devm.getStor post = Devm.getStor parent := by
  by_cases settles : Frame.settlementCommits (Frame.ofCall msg) out = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    have enter : (Frame.ofCall msg).enter = .run cevm :=
      (RunFrame.some_inv process).1
    rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
    simp only [Frame.ofCall] at transfer evmEq
    have preState : cevm.dyna.state = benv.state :=
      congrArg (fun evm : Evm => evm.dyna.state) evmEq
    have postState : post.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost process committed
    funext owner
    change post.state.getStor owner = parent.state.getStor owner
    rw [postState]
    change Devm.getStor (Execution.committedPost out committed) owner = _
    rw [body committed]
    change cevm.dyna.state.getStor owner = parent.state.getStor owner
    rw [preState, parentState, benvAfterTransfer_getStor_eq transfer]
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all
    have rollback := (ProcessMessage.rollback_of_error process postError).1
    funext owner
    change post.state.getStor owner = parent.state.getStor owner
    rw [rollback, parentState]

/-- A recursive instruction whose child frame is static and whose committed
body leaves every storage map equal leaves every storage map equal.  The
child's static flag rules out `CREATE`, whose frames are never static. -/
private theorem xinstSome_getStor
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume}
    {cevm : Evm} {out : Execution}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (childStatic : frame.inner.isStatic = true)
    (frameRun : RunFrame frame (.some ⟨cevm, out⟩) result)
    (resumeRun : resume.run result = .ok post)
    (body : ∀ committed : Execution.commits out = true,
      Devm.getStor (Execution.committedPost out committed) =
        Devm.getStor cevm.dyna) :
    Devm.getStor post = Devm.getStor pre := by
  rcases Xinst.step_shape sevm pre x with
    ⟨execution, shape, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, -⟩
    simp [Jaune.Frame.ofCreate, createMsg, processCreateMessage.msg,
      Msg.withBenv] at childStatic
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    have run : GenericCall sevm d gas value caller target codeAddress stv
        isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨cevm, out⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [spawn]
      exact ⟨result, frameRun, resumeRun.symm⟩
    unfold GenericCall genericCall.step at run
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
    repeat' split at run
    all_goals simp only [XStep.ofExcept, XStep.Run] at run
    · cases run.1
    · cases run.1
    · obtain ⟨settled, process, resumed⟩ := run
      rcases settled with error | child
      · cases Resume.call_run_error resumed.symm
      have childState : post.state = child.state :=
        Resume.call_state resumed.symm
      have settledEq := processMessage_getStor_of_body
        (parent := d.withReturnData []) process rfl body
      funext owner
      change post.state.getStor owner = pre.state.getStor owner
      rw [childState]
      exact (congrFun settledEq owner).trans (hprefix.getStor owner).symm

/-- **Static execution leaves every storage map equal.**  A committing
execution of a static frame ends with exactly its entry `Stor` tree at every
account, children included. -/
theorem Exec.getStor_committedPost_eq_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true) :
    Devm.getStor (Execution.committedPost out committed) =
      Devm.getStor pre := by
  induction run with
  | halt step => exact staticHalt_getStor step committed
  | cont step _ ih =>
      exact (ih static committed).trans (staticStep_cont_getStor step static)
  | doneErr _ _ _ => simp [Execution.commits] at committed
  | @doneOk _ nodeSevm nodePre _ _ _ _ nodePost _ step enter resumeRun _ ih =>
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun : Xinst.Run nodeSevm nodePre x .none (.ok nodePost) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_done enter, resumeRun.symm⟩
      exact (ih static committed).trans (Xinst.none_getStor_eq xrun)
  | runErr _ _ _ _ _ => simp [Execution.commits] at committed
  | runOk step enter _ resumeRun _ childIH nextIH =>
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have childStatic := Evm.step_run_isStatic step enter static
      exact (nextIH static committed).trans
        (xinstSome_getStor spawn (Evm.step_spawn_isStatic step static)
          (RunFrame.of_run enter) resumeRun
          (fun childCommitted => childIH childStatic childCommitted))

/-- Every successful `STATICCALL` leaves every storage map equal, including
when it enters arbitrary interpreted code. -/
theorem Ninst.staticcall_inv_getStor_exact :
    Ninst.Inv Devm.getStor Ninst.staticcall := by
  intro sevm pre post run
  rcases run with ⟨slot, filled, pc, stepRun⟩
  have xrun : Xinst.Run sevm pre .staticcall slot (.ok post) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep,
      Xinst.Run] using stepRun
  cases slot with
  | none => exact (Xinst.none_getStor_eq xrun).symm
  | some child =>
      rcases child with ⟨cevm, out⟩
      rcases filled with ⟨childRun⟩
      rcases XStep.Run.some_inv xrun with ⟨frame, resume, spawn, enter, resumed⟩
      have childStatic : cevm.sta.isStatic = true :=
        (Frame.enter_run_isStatic enter).trans
          (Xinst.step_staticcall_spawn_isStatic spawn)
      exact (xinstSome_getStor spawn (Xinst.step_staticcall_spawn_isStatic spawn)
        (RunFrame.of_run enter) resumed.symm
        (fun committed => Exec.getStor_committedPost_eq_of_static childRun
          childStatic committed)).symm

instance staticcall_getStor_hinv : Ninst.Hinv Devm.getStor Ninst.staticcall :=
  ⟨Ninst.staticcall_inv_getStor_exact⟩

end Blanc
