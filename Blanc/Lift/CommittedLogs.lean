import Blanc.ExecutionStateTrace
import Blanc.Lift.Quiet

/-! Actual successful LOG observations and settlement-retained log chronology. -/

namespace Blanc

open Jaune
open scoped LogOutputHinv

/-- The LOG datum read from the actual decoded instruction and entry machine. -/
def Exec.logAt? (pc : Nat) (sevm : Sevm) (pre : Devm) : Option Log :=
  match Evm.getInst ⟨pc, sevm, pre⟩ with
  | some (.next (.reg (.log n))) =>
      match pre.stack with
      | mi :: sz :: rest =>
          some ⟨sevm.currentTarget, rest.take n.val,
            (pre.memory.read mi.toNat sz.toNat).1⟩
      | _ => none
  | _ => none

/-- Only an actual continued instruction can contribute a successful LOG. -/
def Exec.Deriv.successfulLog? (node : Exec.Deriv) : Option Log :=
  match node.exc with
  | .cont _ _ => Exec.logAt? node.pc node.sevm node.devm
  | _ => none

/-- Entry, settlement and rollback seams do not duplicate child LOGs. -/
def Exec.boundaryOwnLogs (boundary : Exec.StateBoundary) : List Log :=
  match boundary.origin.kind with
  | .instruction =>
      (Exec.Deriv.successfulLog? (Exec.Frame.rootDeriv boundary.origin.driver)).toList
  | _ => []

private theorem Exec.logAt_of_run
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Fin 5}
    (decoded : Evm.getInst ⟨pc, sevm, pre⟩ = some (.next (.reg (.log n))))
    (run : Ninst.Run sevm pre (.reg (.log n)) post) :
    ∃ entry, Exec.logAt? pc sevm pre = some entry ∧
      post.logs = pre.logs ++ [entry] := by
  obtain ⟨mi, sz, topics, length, pop, logs⟩ := of_run_log_val run
  change pre.stack = (mi :: sz :: topics) ++ post.stack at pop
  refine ⟨⟨sevm.currentTarget, topics,
    (pre.memory.read mi.toNat sz.toNat).1⟩, ?_, logs⟩
  simp only [Exec.logAt?, decoded, pop, List.cons_append]
  rw [← length, Jaune.List.take_length_append]

private theorem genericCreate_step_done_logs
    {sevm : Sevm} {pre post : Devm} {endowment : B256} {address : Adr}
    {mi ms : Nat}
    (step : genericCreate.step sevm pre endowment address mi ms =
      .done (.ok post)) : post.logs = pre.logs := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at step
  repeat' split at step
  all_goals simp only [XStep.ofExcept, reduceCtorEq, XStep.done.injEq,
    Except.ok.injEq] at step
  all_goals subst post
  all_goals rename_i pushed pushEq
  all_goals have logs := (Devm.push_of_push pushEq).logs
  all_goals exact logs.symm

private theorem genericCall_step_done_logs
    {sevm : Sevm} {pre post : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    (step : genericCall.step sevm pre gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .done (.ok post)) :
    post.logs = pre.logs := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at step
  repeat' split at step
  all_goals simp only [XStep.ofExcept, reduceCtorEq, XStep.done.injEq,
    Except.ok.injEq] at step
  all_goals subst post
  rename_i pushed pushEq
  have logs := (Devm.push_of_push pushEq).logs
  exact logs.symm

private theorem Xinst_step_done_logs
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Xinst.step sevm pre x = .done (.ok post)) :
    post.logs = pre.logs := by
  rcases Lift.Xinst.step_shapeLogs sevm pre x fork with
    ⟨out, shape, logs⟩ | ⟨_, d, value, address, mi, ms, logs, shape⟩ |
    ⟨d, gas, value, caller, target, codeAddress, stv, isSt,
      ii, isz, oi, osz, code, dp, logs, shape⟩
  · rw [shape] at step
    cases step
    exact logs.symm
  · rw [shape] at step
    exact (genericCreate_step_done_logs step).trans logs
  · rw [shape] at step
    exact (genericCall_step_done_logs step).trans logs

private theorem Exec.cont_logs
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont nextPc post) :
    post.logs = pre.logs ++ (Exec.logAt? pc sevm pre).toList := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      simp only [Evm.step, decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error => rw [jumpEq] at step; cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              simp only [Exec.logAt?, decoded, Option.toList_none, List.append_nil]
              exact Lift.Jinst.logs_of_ok jumpEq
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont nextPc post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq := Ninst.step_cont_pc nstep
          subst nextPc
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | push bytes bound =>
              simp only [Exec.logAt?, decoded, Option.toList_none, List.append_nil]
              exact (Ninst.Hinv.inv (f := Devm.logs)
                (show Ninst.Run sevm pre (.push bytes bound) post from
                  ⟨.none, trivial, pc, nrun⟩)).symm
          | dupn imm =>
              simp only [Exec.logAt?, decoded, Option.toList_none, List.append_nil]
              exact Lift.Ninst.dupn_logs ⟨.none, trivial, pc, nrun⟩
          | swapn imm =>
              simp only [Exec.logAt?, decoded, Option.toList_none, List.append_nil]
              exact Lift.Ninst.swapn_logs ⟨.none, trivial, pc, nrun⟩
          | exchange imm =>
              simp only [Exec.logAt?, decoded, Option.toList_none, List.append_nil]
              exact Lift.Ninst.exchange_logs ⟨.none, trivial, pc, nrun⟩
          | exec executable =>
              simp only [Exec.logAt?, decoded, Option.toList_none, List.append_nil]
              simp only [Ninst.step_exec, XStep.toStep] at nstep
              cases actual : Xinst.step sevm pre executable with
              | spawn frame resume => rw [actual] at nstep; cases nstep
              | done out =>
                  rw [actual] at nstep
                  cases out with
                  | error error => cases nstep
                  | ok actualPost =>
                      cases nstep
                      exact Xinst_step_done_logs fork actual
          | reg regular =>
              have rrun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
                (Step.run_ofExecution.mp nrun).2.symm
              by_cases isLog : ∃ n, regular = .log n
              · obtain ⟨n, rfl⟩ := isLog
                obtain ⟨entry, image, logs⟩ := Exec.logAt_of_run decoded
                  (show Ninst.Run sevm pre (.reg (.log n)) post from
                    ⟨.none, trivial, pc, nrun⟩)
                rw [image]
                exact logs
              · have keeps := Lift.Rinst.logs_of_ok
                  (fun n h => isLog ⟨n, h⟩) rrun
                cases regular
                all_goals try exact (isLog ⟨_, rfl⟩).elim
                all_goals simp only [Exec.logAt?, decoded, Option.toList_none,
                  List.append_nil]
                all_goals exact keeps

private theorem chargeCodeGas_logs (rules : ForkRules) (pre : Devm) :
    Execution.Rel Lift.Devm.LogsEq pre
      (processCreateMessage.chargeCodeGas rules pre) := by
  unfold processCreateMessage.chargeCodeGas
  split
  · dsimp only
    split
    · rfl
    · refine Lift.LogsWalk.bindE rfl (Lift.LogsWalk.chargeGas _ pre) ?_
      intro d logs
      split <;> exact logs.symm
  · dsimp only
    split
    · rfl
    · split
      · rfl
      · refine Lift.LogsWalk.bindE rfl (Lift.LogsWalk.chargeGas _ pre) ?_
        intro d logs
        exact Lift.LogsWalk.leaf logs (Lift.LogsWalk.chargeStateGas _ d)

private theorem processMessage_settle_logs
    {msg : Msg} {pre post : Devm}
    (settle : processMessage.settle msg (.ok pre) = .ok post) :
    post.logs = pre.logs := by
  obtain ⟨d, same, cases⟩ := processMessage.settle_ok_cases settle
  cases same
  rcases cases with ⟨_, eq⟩ | ⟨_, eq⟩
  · rw [← eq]; rfl
  · rw [← eq]

private theorem processCreateMessage_settle_logs
    {msg : Msg} {pre post : Devm}
    (settle : processCreateMessage.settle msg (.ok pre) = .ok post) :
    post.logs = pre.logs := by
  simp only [processCreateMessage.settle, Bind.bind, Except.bind] at settle
  split at settle
  · have logs := chargeCodeGas_logs msg.benv.stat.rules pre
    cases charged : processCreateMessage.chargeCodeGas msg.benv.stat.rules pre with
    | ok d =>
        simp only [charged] at settle logs
        cases settle
        exact logs.symm
    | error error =>
        rcases error with ⟨error, d⟩
        simp only [charged] at settle logs
        cases error with
        | halt reason =>
            dsimp only at settle logs
            split at settle <;> cases settle <;> exact logs.symm
        | revert => cases settle
        | crypto reason => cases settle
        | internal reason => cases settle
  · cases settle
    rfl

private theorem Frame_settleMsg_logs
    {frame : Frame} {pre post : Devm}
    (settle : frame.settleMsg (.ok pre) = .ok post) :
    post.logs = pre.logs := by
  unfold Frame.settleMsg at settle
  cases message : processMessage.settle frame.inner (.ok pre) with
  | error error =>
      rw [message] at settle
      split at settle <;> cases settle
  | ok d =>
      rw [message] at settle
      have logs := processMessage_settle_logs message
      split at settle
      · exact (processCreateMessage_settle_logs settle).trans logs
      · cases settle
        exact logs

private theorem Frame_settle_logs
    {frame : Frame} {pre post : Devm}
    (settle : frame.settle (.ok pre) = .ok post) :
    post.logs = pre.logs := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok] at settle
  exact Frame_settleMsg_logs settle

private theorem Resume_create_logs
    {parent child post : Devm} {address : Adr}
    (resume : (Resume.create parent address).run (.ok child) = .ok post) :
    post.logs = if child.error.isSome then parent.logs else parent.logs ++ child.logs := by
  unfold Resume.run liftToExecution at resume
  dsimp only [Bind.bind, Except.bind] at resume
  split at resume
  · have logs := (Devm.push_of_push resume).logs
    rw [ite_eq_left ‹child.error.isSome = true›]
    exact logs.symm
  · have logs := (Devm.push_of_push resume).logs
    rw [ite_eq_right ‹¬ child.error.isSome = true›]
    exact logs.symm

private def ResumeLogSeed (pre : Devm) (resume : Resume) : Prop :=
  ∃ parent, parent.logs = pre.logs ∧
    ((∃ address, resume = .create parent address) ∨
      ∃ oi os, resume = .call parent oi os)

private theorem genericCreate_step_spawn_logs
    {sevm : Sevm} {pre : Devm} {endowment : B256} {address : Adr}
    {mi ms : Nat} {frame : Frame} {resume : Resume}
    (step : genericCreate.step sevm pre endowment address mi ms =
      .spawn frame resume) : ResumeLogSeed pre resume := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at step
  repeat' split at step
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at step
  obtain ⟨_, rfl⟩ := step
  refine ⟨addAccessedAddress
    (((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData
      []).incrNonce sevm.currentTarget) address, rfl, Or.inl ⟨address, rfl⟩⟩

private theorem genericCall_step_spawn_logs
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {frame : Frame} {resume : Resume}
    (step : genericCall.step sevm pre gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .spawn frame resume) :
    ResumeLogSeed pre resume := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at step
  repeat' split at step
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at step
  obtain ⟨_, rfl⟩ := step
  exact ⟨pre.withReturnData [], rfl, Or.inr ⟨oi, osz, rfl⟩⟩

private theorem ResumeLogSeed.trans {pre middle : Devm} {resume : Resume}
    (seed : ResumeLogSeed middle resume) (logs : middle.logs = pre.logs) :
    ResumeLogSeed pre resume := by
  obtain ⟨parent, parentLogs, kind⟩ := seed
  exact ⟨parent, parentLogs.trans logs, kind⟩

private theorem Evm_spawn_logs
    {pc nextPc : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc) :
    ResumeLogSeed pre resume ∧ frame.inner.benv.stat = sevm.benvStat := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  refine ⟨?_, Xinst.step_spawn_benvStat spawn⟩
  rcases Lift.Xinst.step_shapeLogs sevm pre x fork with
    ⟨out, shape, logs⟩ | ⟨_, d, value, address, mi, ms, logs, shape⟩ |
    ⟨d, gas, value, caller, target, codeAddress, stv, isSt,
      ii, isz, oi, osz, code, dp, logs, shape⟩
  · rw [shape] at spawn
    cases spawn
  · exact (genericCreate_step_spawn_logs (shape.symm.trans spawn)).trans logs
  · exact (genericCall_step_spawn_logs (shape.symm.trans spawn)).trans logs

private theorem ResumeLogSeed.result_logs
    {pre post : Devm} {resume : Resume}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (seed : ResumeLogSeed pre resume)
    (run : resume.run result = .ok post) :
    ∃ child, result = .ok child ∧
      post.logs = if child.error.isSome then pre.logs else pre.logs ++ child.logs := by
  obtain ⟨parent, logs, kind⟩ := seed
  rcases kind with ⟨address, rfl⟩ | ⟨oi, os, rfl⟩
  · cases result with
    | error error => exact (Resume.create_run_error run).elim
    | ok child =>
        refine ⟨child, rfl, ?_⟩
        rw [Resume_create_logs run, logs]
  · cases result with
    | error error => exact (Resume.call_run_error run).elim
    | ok child =>
        refine ⟨child, rfl, ?_⟩
        rw [Resume.call_logs run, logs]

private theorem Frame_enter_run_logs
    {frame : Frame} {child : Evm}
    (fork : CoveredFork frame.inner.benv.stat.fork)
    (enter : frame.enter = .run child) : child.dyna.logs = [] := by
  obtain ⟨benv, transfer, rfl⟩ := Frame.enter_run_inv enter
  apply Lift.initDevm_logs
  change benv.stat.rules.stateGas = none
  rw [benvAfterTransfer_stat transfer]
  exact fork.rules_stateGas_none

private theorem Devm_subBal_logs
    {pre post : Devm} {address : Adr} {value : B256}
    (run : pre.subBal address value = some post) : post.logs = pre.logs := by
  unfold Devm.subBal at run
  obtain ⟨state, _, same⟩ := Option.bind_eq_some_iff.mp run
  cases same
  rfl

private theorem Linst_selfdestruct_logs
    {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) :
    post.logs = pre.logs := by
  simp only [Linst.Run, Linst.run, fork.rules_stateGas_none] at run
  obtain ⟨⟨donee, d1⟩, pop, rest⟩ := Except.bind_eq_ok run
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at rest
  obtain ⟨d2, charge, rest⟩ := Except.bind_eq_ok rest
  obtain ⟨_, _, rest⟩ := Except.bind_eq_ok rest
  obtain ⟨d3, sub, rest⟩ := Except.bind_eq_ok rest
  have readLogs :
      ((d1.balReadAccount sevm.benvStat.rules donee).balReadAccount
        sevm.benvStat.rules sevm.currentTarget).logs = d1.logs := by
    rw [Devm.balReadAccount_logs, Devm.balReadAccount_logs]
  have accessedLogs : d2.logs = d1.logs := by
    have logs := (Devm.burn_of_chargeGas charge).logs
    rw [← logs]
    split <;> exact readLogs
  have subLogs : d3.logs = d2.logs := by
    unfold Option.toExcept at sub
    split at sub
    · cases sub
    · cases sub
      exact Devm_subBal_logs ‹_ = some _›
  have finalLogs : post.logs = d3.logs := by
    split at rest <;> cases rest <;> rfl
  obtain ⟨word, _, popWord⟩ := Devm.pop_of_popToAdr pop
  exact ((finalLogs.trans subLogs).trans accessedLogs).trans
    (Devm.pop_of_pop popWord).logs.symm

private theorem Linst_logs_of_ok
    {sevm : Sevm} {pre post : Devm} {last : Linst}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : Linst.Run sevm pre last (.ok post)) : post.logs = pre.logs := by
  cases last with
  | stop => exact (Linst.Hinv.inv (f := Devm.logs) (g := Devm.logs) run).symm
  | return_ => exact (Linst.Hinv.inv (f := Devm.logs) (g := Devm.logs) run).symm
  | revert => exact (Lift.Linst.revert_not_ok run).elim
  | selfdestruct => exact Linst_selfdestruct_logs fork run

private theorem Evm_halt_logs
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt (.ok post)) :
    post.logs = pre.logs := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      simp only [Evm.step, decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | next instruction =>
          rw [Evm.step_next decoded] at step
          cases instruction with
          | exec executable =>
              simp only [Ninst.step_exec, XStep.toStep] at step
              split at step
              · exact (Step.ofExecution_ne_halt_ok step).elim
              · cases step
          | reg regular => exact (Step.ofExecution_ne_halt_ok step).elim
          | push bytes bound => exact (Step.ofExecution_ne_halt_ok step).elim
          | dupn imm => exact (Step.ofExecution_ne_halt_ok step).elim
          | swapn imm => exact (Step.ofExecution_ne_halt_ok step).elim
          | exchange imm => exact (Step.ofExecution_ne_halt_ok step).elim
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases actual : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error => rw [actual] at step; cases step
          | ok pair => rw [actual] at step; cases step
      | last last =>
          rw [Evm.step_last decoded] at step
          exact Linst_logs_of_ok fork (Step.halt.inj step)

private theorem Frame_settleMsg_error
    (frame : Frame) (error : EvmError × State × AdrSet × Tra) :
    frame.settleMsg (.error error) = .error error := by
  simp only [Frame.settleMsg, processMessage.settle, processCreateMessage.settle,
    Bind.bind, Except.bind]
  split <;> rfl

private theorem executePrecomp_logs (evm : Evm) (address : Adr) :
    Execution.Rel Lift.Devm.LogsEq evm.dyna (executePrecomp evm address) := by
  unfold executePrecomp applyPrecompResult
  split <;> rfl

private theorem Frame_enter_done_clean_logs
    {frame : Frame} {child : Devm}
    (fork : CoveredFork frame.inner.benv.stat.fork)
    (enter : frame.enter = .done (.ok child))
    (clean : child.error.isNone = true) : child.logs = [] := by
  unfold Frame.enter at enter
  cases transfer : frame.inner.benvAfterTransfer with
  | error error =>
      simp only [transfer, Frame_settleMsg_error] at enter
      cases enter
  | ok benv =>
      simp only [transfer] at enter
      cases started : executeCode.enter (frame.inner.withBenv benv) with
      | inl evm => rw [started] at enter; cases enter
      | inr raw =>
          rw [started] at enter
          have settled : frame.settle raw = .ok child := FrameEntry.done.inj enter
          have commits : Frame.settlementCommits frame raw = true := by
            simp only [Frame.settlementCommits, settled]
            exact clean
          have rawCommits := Frame.raw_commits_of_settlementCommits commits
          have initialLogs : (initEvm (frame.inner.withBenv benv)).dyna.logs = [] := by
            apply Lift.initDevm_logs
            change benv.stat.rules.stateGas = none
            rw [benvAfterTransfer_stat transfer]
            exact fork.rules_stateGas_none
          unfold executeCode.enter at started
          split at started
          · cases started
          · split at started
            · rename_i address decoded enabled
              cases started
              have rawLogs := executePrecomp_logs
                (initEvm (frame.inner.withBenv benv)) address
              cases prec : executePrecomp (initEvm (frame.inner.withBenv benv)) address with
              | error error =>
                  simp only [prec, Execution.commits] at rawCommits
                  cases rawCommits
              | ok d =>
                  rw [prec] at settled rawLogs
                  exact ((Frame_settle_logs settled).trans rawLogs.symm).trans initialLogs
            · cases started

private theorem Evm_childless_logs
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (enter : frame.enter = .done result)
    (resumed : resume.run result = .ok post) : post.logs = pre.logs := by
  obtain ⟨seed, stat⟩ := Evm_spawn_logs fork step
  obtain ⟨child, rfl, logs⟩ := seed.result_logs resumed
  by_cases error : child.error.isSome = true
  · rw [ite_eq_left error] at logs
    exact logs
  · have clean : child.error.isNone = true := by
      cases present : child.error with
      | none => rfl
      | some reason => exact (error (by rw [present]; rfl)).elim
    have childFork : CoveredFork frame.inner.benv.stat.fork := by
      rw [stat]; exact fork
    rw [ite_eq_right error, Frame_enter_done_clean_logs childFork enter clean,
      List.append_nil] at logs
    exact logs

private theorem Evm_resumed_committed_logs
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {raw : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (commits : Frame.settlementCommits frame raw = true) :
    post.logs = pre.logs ++
      (Execution.committedPost raw (Frame.raw_commits_of_settlementCommits commits)).logs := by
  obtain ⟨seed, _⟩ := Evm_spawn_logs fork step
  obtain ⟨child, settled, logs⟩ := seed.result_logs resumed
  have clean : child.error.isNone = true := by
    simpa only [Frame.settlementCommits, settled] using commits
  have notSome : ¬ child.error.isSome = true := by
    cases present : child.error with
    | none => exact Bool.false_ne_true
    | some reason =>
        simp only [present, Option.isNone_some, Bool.false_eq_true] at clean
  rw [ite_eq_right notSome] at logs
  cases raw with
  | error error =>
      have rawCommits := Frame.raw_commits_of_settlementCommits commits
      simp only [Execution.commits, Bool.false_eq_true] at rawCommits
  | ok d =>
      change post.logs = pre.logs ++ d.logs
      rw [logs, Frame_settle_logs settled]

private theorem Evm_resumed_rollback_logs
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {raw : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (notCommits : ¬ Frame.settlementCommits frame raw = true) :
    post.logs = pre.logs := by
  obtain ⟨seed, _⟩ := Evm_spawn_logs fork step
  obtain ⟨child, settled, logs⟩ := seed.result_logs resumed
  have error : child.error.isSome = true := by
    cases present : child.error with
    | some reason => rfl
    | none =>
        apply False.elim
        apply notCommits
        simp only [Frame.settlementCommits, settled, present, Option.isNone_none]
  rw [ite_eq_left error] at logs
  exact logs

private theorem Exec.stateBoundaries_logs_of_commits
    (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork) :
    (Execution.committedPost out committed).logs =
      pre.logs ++
        (Exec.stateBoundariesOfCommits framePath nextChild run committed).flatMap
          Exec.boundaryOwnLogs := by
  induction run generalizing framePath nextChild with
  | @halt actualPc actualSevm actualPre actualOut step =>
      cases actualOut with
      | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
      | ok post =>
          simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons,
            List.flatMap_nil, Exec.boundaryOwnLogs, Exec.stateBoundary,
            List.append_nil, Execution.committedPost]
          exact Evm_halt_logs fork step
  | cont step next ih =>
      simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons,
        Exec.boundaryOwnLogs, Exec.stateBoundary, Exec.Frame.rootDeriv,
        Exec.Frame.ofRun, Exec.Deriv.successfulLog?]
      rw [ih framePath nextChild committed fork, Exec.cont_logs fork step,
        List.append_assoc]
  | doneErr step enter resume =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
      simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons,
        Exec.boundaryOwnLogs, Exec.stateBoundary, List.nil_append]
      rw [ih framePath (nextChild + 1) committed fork,
        Evm_childless_logs fork step enter resume]
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resume next childIh nextIh =>
      simp only [Exec.stateBoundariesOfCommits]
      split
      next childSettles =>
        let childCommitted := Frame.raw_commits_of_settlementCommits childSettles
        have childFork := Evm.step_spawn_child_fork step enter fork
        have childLogs := childIh (framePath ++ [nextChild]) 0 childCommitted childFork
        have initialLogs := Frame_enter_run_logs
          (show CoveredFork _ from by
            rw [(Evm_spawn_logs fork step).2]
            exact fork) enter
        simp only [List.flatMap_cons, List.flatMap_append, Exec.boundaryOwnLogs,
          Exec.stateBoundary, List.nil_append]
        rw [nextIh framePath (nextChild + 1) committed fork,
          Evm_resumed_committed_logs fork step resume childSettles, childLogs,
          initialLogs, List.nil_append, List.append_assoc]
      next childDoesNotSettle =>
        simp only [List.flatMap_cons, Exec.boundaryOwnLogs, Exec.stateBoundary,
          List.nil_append]
        rw [nextIh framePath (nextChild + 1) committed fork,
          Evm_resumed_rollback_logs fork step resume childDoesNotSettle]

/-- Exact committed endpoint logs in the existing retained chronological traversal.
Only successful LOG instructions emit; child settlement contributes no duplicate.
Complete failed settlement erases the entire child subtree. -/
theorem Exec.committed_logs
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork) :
    (Execution.committedPost out committed).logs =
      pre.logs ++ (Exec.committedStateBoundaries run).flatMap Exec.boundaryOwnLogs := by
  simp only [Exec.committedStateBoundaries, committed, dite_true]
  exact Exec.stateBoundaries_logs_of_commits [] 0 run committed fork

private theorem Exec.logAt_some_decoded
    {pc : Nat} {sevm : Sevm} {pre : Devm} {entry : Log}
    (image : Exec.logAt? pc sevm pre = some entry) :
    ∃ n, Evm.getInst ⟨pc, sevm, pre⟩ = some (.next (.reg (.log n))) := by
  unfold Exec.logAt? at image
  split at image
  · rename_i n decoded
    exact ⟨n, decoded⟩
  · cases image

/-- A projected LOG has an actual decoded LOG instruction and a successful
driver step, with precisely that entry appended to the pre-instruction logs. -/
theorem Exec.Deriv.successfulLog?_sound
    {node : Exec.Deriv} {entry : Log}
    (image : Exec.Deriv.successfulLog? node = some entry) :
    ∃ n nextPc post,
      Evm.getInst ⟨node.pc, node.sevm, node.devm⟩ = some (.next (.reg (.log n))) ∧
      Evm.step ⟨node.pc, node.sevm, node.devm⟩ = .cont nextPc post ∧
      post.logs = node.devm.logs ++ [entry] := by
  obtain ⟨pc, sevm, pre, out, run⟩ := node
  cases run with
  | @cont pc sevm pre nextPc post out step next =>
      change Exec.logAt? pc sevm pre = some entry at image
      obtain ⟨n, decoded⟩ := Exec.logAt_some_decoded image
      have nstep : Ninst.step ⟨pc, sevm, pre⟩ (.reg (.log n)) =
          .cont nextPc post := by
        rw [← Evm.step_next decoded]
        exact step
      have nrun : Ninst.StepRun pc sevm pre (.reg (.log n)) .none (.ok post) := by
        unfold Ninst.StepRun
        rw [nstep]
        exact ⟨rfl, rfl⟩
      obtain ⟨actual, same, logs⟩ := Exec.logAt_of_run decoded
        (show Ninst.Run sevm pre (.reg (.log n)) post from
          ⟨.none, trivial, pc, nrun⟩)
      have sameEntry : actual = entry := Option.some.inj (same.symm.trans image)
      subst actual
      exact ⟨n, nextPc, post, decoded, step, logs⟩
  | halt step => cases image
  | doneErr step enter resume => cases image
  | doneOk step enter resume next => cases image
  | runErr step enter child resume => cases image
  | runOk step enter child resume next => cases image

end Blanc
