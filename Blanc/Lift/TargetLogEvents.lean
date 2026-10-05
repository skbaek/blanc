import Blanc.Lift.SegmentedHistory
import Blanc.Lift.CommittedLogs
import Blanc.Lift.ReachChain
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionTraceCalldata
import Blanc.ExecutionNoninterference
import Blanc.Lift.Sound

/-!
# Retained target frames interleaved with actual foreign LOGs

A committed execution observed from one storage owner `ca` is, in chronological retained
order, a list of actual successful LOGs emitted by foreign frames and of retained frames
whose current target is `ca` (each such frame stops the traversal and is consumed whole).
`Exec.targetLogEventsFrom` is that list; its frame projection is exactly the existing
`Exec.retainedTargetFramesFromAt`. The per-step transport lemmas below say what a foreign
step does to `ca`'s storage and to the log list, for any callee code. Nothing here mentions
a contract.
-/

namespace Blanc

open Jaune

/-- Retained chronological events seen from the storage owner `ca`: actual foreign LOGs
and selected target frames. A failing child settlement discards its whole subtree. -/
def Exec.targetLogEventsFrom (ca : Adr) (path : List Nat) (counter : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List (Log ⊕ Exec.LocatedFrame) :=
  if sevm.currentTarget = ca then
    [.inr ⟨path, Exec.Frame.ofRun run committed⟩]
  else
    match run with
    | .halt _ => []
    | .cont _ next =>
        (Exec.logAt? pc sevm pre).toList.map Sum.inl ++
          Exec.targetLogEventsFrom ca path counter next committed
    | .doneErr _ _ _ => by simp only [Execution.commits, Bool.false_eq_true] at committed
    | .doneOk _ _ _ next => Exec.targetLogEventsFrom ca path (counter + 1) next committed
    | .runErr _ _ _ _ => by simp only [Execution.commits, Bool.false_eq_true] at committed
    | .runOk (f := frame) (raw := raw) _ _ child _ next =>
        (if h : Frame.settlementCommits frame raw = true then
          Exec.targetLogEventsFrom ca (path ++ [counter]) 0 child
            (Frame.raw_commits_of_settlementCommits h)
         else []) ++
          Exec.targetLogEventsFrom ca path (counter + 1) next committed
termination_by sizeOf run

theorem Exec.targetLogEventsFrom_target (ca : Adr) (path : List Nat) (counter : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (target : sevm.currentTarget = ca) :
    Exec.targetLogEventsFrom ca path counter run committed =
      [.inr ⟨path, Exec.Frame.ofRun run committed⟩] := by
  rw [Exec.targetLogEventsFrom.eq_def, ite_eq_left target]

theorem Exec.targetLogEventsFrom_halt (ca : Adr) (path : List Nat) (counter : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (committed : Execution.commits out = true) (foreign : sevm.currentTarget ≠ ca) :
    Exec.targetLogEventsFrom ca path counter (.halt step) committed = [] := by
  rw [Exec.targetLogEventsFrom.eq_def, ite_eq_right foreign]

theorem Exec.targetLogEventsFrom_cont (ca : Adr) (path : List Nat) (counter : Nat)
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter)
    (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true) (foreign : sevm.currentTarget ≠ ca) :
    Exec.targetLogEventsFrom ca path counter (.cont step next) committed =
      (Exec.logAt? pc sevm pre).toList.map Sum.inl ++
        Exec.targetLogEventsFrom ca path counter next committed := by
  conv_lhs => rw [Exec.targetLogEventsFrom, ite_eq_right foreign]

theorem Exec.targetLogEventsFrom_doneOk (ca : Adr) (path : List Nat) (counter : Nat)
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {result : Except (EvmError × State × AdrSet × Tra) Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (entered : frame.enter = .done result)
    (resumed : resume.run result = .ok inter) (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true) (foreign : sevm.currentTarget ≠ ca) :
    Exec.targetLogEventsFrom ca path counter (.doneOk step entered resumed next) committed =
      Exec.targetLogEventsFrom ca path (counter + 1) next committed := by
  conv_lhs => rw [Exec.targetLogEventsFrom, ite_eq_right foreign]

theorem Exec.targetLogEventsFrom_runOk (ca : Adr) (path : List Nat) (counter : Nat)
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (entered : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok inter)
    (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true) (foreign : sevm.currentTarget ≠ ca) :
    Exec.targetLogEventsFrom ca path counter
        (.runOk step entered child resumed next) committed =
      (if settles : Frame.settlementCommits frame raw = true then
        Exec.targetLogEventsFrom ca (path ++ [counter]) 0 child
          (Frame.raw_commits_of_settlementCommits settles)
       else []) ++
        Exec.targetLogEventsFrom ca path (counter + 1) next committed := by
  conv_lhs => rw [Exec.targetLogEventsFrom, ite_eq_right foreign]

/-- The frame projection is exactly the existing retained target traversal. -/
theorem Exec.targetLogEventsFrom_frames (ca : Adr) (path : List Nat) (counter : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    (Exec.targetLogEventsFrom ca path counter run committed).filterMap Sum.getRight? =
      Exec.retainedTargetFramesFromAt ca path counter run committed := by
  induction run generalizing path counter with
  | @halt pc sevm pre out step =>
    by_cases target : sevm.currentTarget = ca
    · rw [Exec.targetLogEventsFrom_target _ _ _ _ committed target,
        Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
      rfl
    · rw [Exec.targetLogEventsFrom_halt _ _ _ step committed target,
        Exec.retainedTargetFramesFromAt_halt _ _ _ step committed target]
      rfl
  | @cont pc sevm pre pc' inter out step next ih =>
    by_cases target : sevm.currentTarget = ca
    · rw [Exec.targetLogEventsFrom_target _ _ _ _ committed target,
        Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
      rfl
    · rw [Exec.targetLogEventsFrom_cont _ _ _ step next committed target,
        Exec.retainedTargetFramesFromAt_cont _ _ _ step next committed target,
        List.filterMap_append, ih path counter committed]
      cases (Exec.logAt? pc sevm pre) <;> rfl
  | doneErr step enter resumed =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre callee resume pc' result inter out step enter resumed next ih =>
    by_cases target : sevm.currentTarget = ca
    · rw [Exec.targetLogEventsFrom_target _ _ _ _ committed target,
        Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
      rfl
    · rw [Exec.targetLogEventsFrom_doneOk _ _ _ step enter resumed next committed target,
        Exec.retainedTargetFramesFromAt_doneOk _ _ _ step enter resumed next committed target]
      exact ih path (counter + 1) committed
  | runErr step enter child resumed childIH =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre callee resume pc' childEvm raw inter out step enter child resumed next
      childIH nextIH =>
    by_cases target : sevm.currentTarget = ca
    · rw [Exec.targetLogEventsFrom_target _ _ _ _ committed target,
        Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
      rfl
    · rw [Exec.targetLogEventsFrom_runOk _ _ _ step enter child resumed next committed target,
        Exec.retainedTargetFramesFromAt_runOk _ _ _ step enter child resumed next committed target,
        List.filterMap_append, nextIH path (counter + 1) committed]
      by_cases settles : Frame.settlementCommits callee raw = true
      · rw [dite_eq_left settles, dite_eq_left settles,
          childIH (path ++ [counter]) 0 (Frame.raw_commits_of_settlementCommits settles)]
      · rw [dite_eq_right settles, dite_eq_right settles]
        rfl

/-! ## Storage of `ca` across one foreign step -/

/-- A same-frame step of a frame other than `ca` keeps `ca`'s storage. -/
theorem Evm.step_cont_getStor_foreign {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {ca : Adr} (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (foreign : sevm.currentTarget ≠ ca) :
    Devm.getStor post ca = Devm.getStor pre ca := by
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
              have frame := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              exact (frame.getStor ca).symm
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size := Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          exact Ninst.foreignNone_getStor_eq fork nrun foreign

/-- A childless message leaves every storage map unchanged. -/
theorem Evm.step_done_getStor {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (entered : frame.enter = .done result)
    (resumed : resume.run result = .ok inter) :
    Devm.getStor inter = Devm.getStor pre := by
  rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
  have xrun : Xinst.Run sevm pre x .none (.ok inter) := by
    unfold Xinst.Run XStep.Run
    rw [spawn]
    exact ⟨_, RunFrame.of_done entered, resumed.symm⟩
  exact Xinst.none_getStor_eq xrun

/-- A child entered by an executable instruction opens on its parent's storage at every
code-bearing account, at pc zero with an empty machine and output, under the parent's block
environment, with short calldata. -/
theorem Xinst.spawn_child_world {sevm : Sevm} {pre : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume} {child : Evm}
    (fork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (entered : frame.enter = .run child) :
    (∀ ca, pre.getCode ca ≠ .empty → Devm.getStor child.dyna ca = Devm.getStor pre ca) ∧
      child.pc = 0 ∧
      (child.dyna.stack = [] ∧ child.dyna.memory = Mem.empty ∧ child.dyna.output = []) ∧
      child.sta.benvStat = sevm.benvStat ∧ CoveredFork child.sta.benvStat.fork ∧
      child.sta.data.length < 2 ^ 256 := by
  have stat : child.sta.benvStat = sevm.benvStat :=
    (Jaune.Frame.enter_run_benvStat entered).trans (Xinst.step_spawn_benvStat spawn)
  refine ⟨?_, Frame.enter_run_pc entered, ?_, stat, by rw [stat]; exact fork, ?_⟩
  · intro ca nonempty
    obtain ⟨storage, _⟩ := Xinst.step_spawn_world fork spawn nonempty
    obtain ⟨benv, transfer, rfl⟩ := Frame.enter_run_inv entered
    exact (congrFun (benvAfterTransfer_getStor_eq transfer) ca).trans storage
  · refine ⟨?_, ?_, Frame.enter_run_output_empty entered⟩
    · obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv entered
      rfl
    · obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv entered
      rfl
  · rw [ExecutionTrace.Frame.enter_data_eq entered]
    exact ExecutionTrace.Xinst.step_spawn_inner_data_length_lt fork.rules_stateGas_none spawn

/-- An entered child message leaves a code-bearing account's storage as the child's
committed endpoint when it settles, and as before the call when it rolls back. -/
theorem Xinst.spawn_run_getStor {sevm : Sevm} {pre inter : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (entered : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok inter)
    {ca : Adr} (nonempty : pre.getCode ca ≠ .empty) :
    (∀ settles : Frame.settlementCommits frame raw = true, ∀ key,
      (Devm.getStor inter ca).get key =
        (Devm.getStor (Execution.committedPost raw
          (Frame.raw_commits_of_settlementCommits settles)) ca).get key) ∧
    (¬ Frame.settlementCommits frame raw = true → ∀ key,
      (Devm.getStor inter ca).get key = (Devm.getStor pre ca).get key) := by
  obtain ⟨world, _, _, _, childFork, _⟩ := Xinst.spawn_child_world fork spawn entered
  have replay := Xinst.storageReplay_some_of_body spawn (RunFrame.of_run entered) resumed
    (fun committed => Exec.storageReplay_committedPost child committed childFork) fork
  have entry := world ca nonempty
  refine ⟨?_, ?_⟩
  · intro settles key
    rw [ite_eq_left settles] at replay
    have body := Exec.storageReplay_committedPost child
      (Frame.raw_commits_of_settlementCommits settles) childFork ca key
    rw [replay ca key, body, entry]
  · intro rolled key
    rw [ite_eq_right rolled] at replay
    simpa only [Exec.StorageWrite.replayCell, List.foldl_nil] using replay ca key

/-- The same storage transport at a driver spawn. -/
theorem Evm.step_run_getStor {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (entered : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok inter)
    {ca : Adr} (nonempty : pre.getCode ca ≠ .empty) :
    (∀ settles : Frame.settlementCommits frame raw = true, ∀ key,
      (Devm.getStor inter ca).get key =
        (Devm.getStor (Execution.committedPost raw
          (Frame.raw_commits_of_settlementCommits settles)) ca).get key) ∧
    (¬ Frame.settlementCommits frame raw = true → ∀ key,
      (Devm.getStor inter ca).get key = (Devm.getStor pre ca).get key) := by
  rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
  exact Xinst.spawn_run_getStor fork spawn entered child resumed nonempty

/-- A CALL or STATICCALL child of any frame runs the installed image of `ca` when it
executes at `ca`. -/
theorem CodeSem.At.callChild {sem : CodeSem} {ca : Adr} {sevm : Sevm} {pre : Devm}
    {x : Xinst} {frame : Jaune.Frame} {resume : Resume} {child : Evm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (entered : frame.enter = .run child) (callFamily : x = .call ∨ x = .staticcall)
    (installed : some (pre.getCode ca).toList = sem.image) :
    sem.At ca child.pc child.sta child.dyna := by
  have nonempty : pre.getCode ca ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed, empty, ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  refine ⟨?_, fun target => ⟨?_, Frame.enter_run_pc entered⟩⟩
  · rw [Frame.enter_run_getCode entered ca, Xinst.step_spawn_getCode spawn ca]
    exact installed
  · have innerTarget : frame.inner.currentTarget = ca :=
      (Frame.enter_run_currentTarget entered).symm.trans target
    have notDelegation : ¬ isValidDelegation (pre.getCode frame.inner.currentTarget) := by
      rw [innerTarget]
      exact sem.not_delegation installed
    have codeEq : frame.inner.code = pre.getCode frame.inner.currentTarget := by
      rcases Xinst.step_spawn_source spawn with empty | same | source
      · rw [innerTarget] at empty
        exact (nonempty empty).elim
      · rcases callFamily with rfl | rfl
        · exact Xinst.step_call_sameTarget_code spawn same notDelegation
        · exact Xinst.step_staticcall_sameTarget_code spawn same notDelegation
      · exact source notDelegation
    rw [Frame.enter_run_code entered, codeEq, innerTarget]
    exact installed

/-- Selected frames of the retained traversal are raw frame roots of the run, at `ca`. -/
theorem Exec.retainedTargetFramesFromAt_rawFrameRoot (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    {located : Exec.LocatedFrame}
    (member : located ∈ Exec.retainedTargetFramesFromAt ca [] 0 run committed) :
    Exec.Frame.rootDeriv located.frame ∈ Exec.rawFrameRoots run ∧
      located.frame.sevm.currentTarget = ca := by
  have same : Exec.retainedTargetFramesFromAt ca [] 0 run committed =
      (Exec.retainedTargetTurns ca run).filterMap Sum.getRight? := by
    rw [← Exec.retainedTargetTurnsAt_filterMap_eq ca [] run committed]
    rfl
  rw [same] at member
  obtain ⟨ordered, owned, _⟩ := Exec.retainedTargetTurns_spec ca run
  refine ⟨Exec.mem_rawFrameRoots_of_mem_committedFrames run located.frame ?_,
    owned located member⟩
  rw [← Exec.committedFramePaths_map_frame]
  exact List.mem_map_of_mem (ordered.subset member)

/-! ## Logs across one step, from the public committed-log chronology -/

private theorem Exec.stateBoundariesOfCommits_ownLogs_path
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (path path' : List Nat) (counter counter' : Nat) :
    (Exec.stateBoundariesOfCommits path counter run committed).flatMap Exec.boundaryOwnLogs =
      (Exec.stateBoundariesOfCommits path' counter' run committed).flatMap
        Exec.boundaryOwnLogs := by
  induction run generalizing path path' counter counter' with
  | halt step =>
    simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, List.flatMap_nil,
      Exec.boundaryOwnLogs, Exec.stateBoundary]
  | cont step next ih =>
    simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.boundaryOwnLogs,
      Exec.stateBoundary]
    rw [ih committed path path' counter counter']
  | doneErr step enter resume =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
    simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.boundaryOwnLogs,
      Exec.stateBoundary, List.nil_append]
    exact ih committed path path' (counter + 1) (counter' + 1)
  | runErr step enter child resume ih =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resume next childIh nextIh =>
    simp only [Exec.stateBoundariesOfCommits]
    split
    next settles =>
      simp only [List.flatMap_cons, List.flatMap_append, Exec.boundaryOwnLogs,
        Exec.stateBoundary, List.nil_append]
      rw [childIh (Frame.raw_commits_of_settlementCommits settles) (path ++ [counter])
          (path' ++ [counter']) 0 0,
        nextIh committed path path' (counter + 1) (counter' + 1)]
    next rolled =>
      simp only [List.flatMap_cons, Exec.boundaryOwnLogs, Exec.stateBoundary,
        List.nil_append]
      exact nextIh committed path path' (counter + 1) (counter' + 1)

/-- Committed endpoint logs at any original path and counter. -/
theorem Exec.committed_logs_at
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork) (path : List Nat) (counter : Nat) :
    (Execution.committedPost out committed).logs =
      pre.logs ++ (Exec.stateBoundariesOfCommits path counter run committed).flatMap
        Exec.boundaryOwnLogs := by
  have logs := Exec.committed_logs run committed fork
  simp only [Exec.committedStateBoundaries, committed, dite_true] at logs
  rw [logs, Exec.stateBoundariesOfCommits_ownLogs_path run committed [] path 0 counter]

/-- One same-frame step appends exactly its own successful LOG, if any. -/
theorem Exec.cont_logs_eq {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {out : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter) (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true) :
    inter.logs = pre.logs ++ (Exec.logAt? pc sevm pre).toList := by
  have whole := Exec.committed_logs_at (.cont step next) committed fork [] 0
  have rest := Exec.committed_logs_at next committed fork [] 0
  simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.boundaryOwnLogs,
    Exec.stateBoundary, Exec.Frame.rootDeriv, Exec.Frame.ofRun,
    Exec.Deriv.successfulLog?] at whole
  rw [whole, ← List.append_assoc] at rest
  exact (List.append_cancel_right rest).symm

/-- A childless message adds no log. -/
theorem Exec.doneOk_logs_eq {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {result : Except (EvmError × State × AdrSet × Tra) Devm} {out : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (entered : frame.enter = .done result)
    (resumed : resume.run result = .ok inter) (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true) :
    inter.logs = pre.logs := by
  have whole := Exec.committed_logs_at (.doneOk step entered resumed next) committed fork [] 0
  have rest := Exec.committed_logs_at next committed fork [] 1
  simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.boundaryOwnLogs,
    Exec.stateBoundary, List.nil_append] at whole
  rw [whole] at rest
  exact (List.append_cancel_right rest).symm

/-- An entered child adds exactly its own committed logs when it settles, and none when
it rolls back. -/
theorem Exec.runOk_logs_eq {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm} {raw out : Execution}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (entered : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok inter)
    (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true) :
    (∀ settles : Frame.settlementCommits frame raw = true, ∃ L,
      (Execution.committedPost raw (Frame.raw_commits_of_settlementCommits settles)).logs =
        childEvm.dyna.logs ++ L ∧ inter.logs = pre.logs ++ L) ∧
    (¬ Frame.settlementCommits frame raw = true → inter.logs = pre.logs) := by
  have whole := Exec.committed_logs_at (.runOk step entered child resumed next) committed
    fork [] 0
  have rest := Exec.committed_logs_at next committed fork [] 1
  simp only [Exec.stateBoundariesOfCommits] at whole
  refine ⟨?_, ?_⟩
  · intro settles
    have childFork := Evm.step_spawn_child_fork step entered fork
    refine ⟨_, Exec.committed_logs_at child (Frame.raw_commits_of_settlementCommits settles)
      childFork ([] ++ [0]) 0, ?_⟩
    rw [dite_eq_left settles] at whole
    simp only [List.flatMap_cons, List.flatMap_append, Exec.boundaryOwnLogs,
      Exec.stateBoundary, List.nil_append] at whole
    rw [whole, ← List.append_assoc] at rest
    exact (List.append_cancel_right rest).symm
  · intro rolled
    rw [dite_eq_right rolled] at whole
    simp only [List.flatMap_cons, Exec.boundaryOwnLogs, Exec.stateBoundary,
      List.nil_append] at whole
    rw [whole] at rest
    exact (List.append_cancel_right rest).symm

/-! ## The installed image across foreign steps and into children -/

/-- A same-frame edge of a foreign frame keeps the installed image. -/
theorem CodeSem.At.parentStep {sem : CodeSem} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (next : Exec pc' sevm inter out)
    (edge : Exec.Deriv.ParentStep ⟨pc', sevm, inter, out, next⟩ ⟨pc, sevm, pre, out, run⟩)
    (installed : sem.At ca pc sevm pre) (foreign : sevm.currentTarget ≠ ca) :
    sem.At ca pc' sevm inter := by
  have nonempty : (pre.getCode ca).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve edge ca nonempty
  refine ⟨?_, fun target => (foreign target).elim⟩
  rw [codeEq]
  exact installed.1

/-- A child entered from a foreign frame opens on the same installed image and storage of
`ca`, with an empty machine and output, the parent's block environment and a covered fork. -/
theorem CodeSem.At.spawnChild {sem : CodeSem} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {callee : Jaune.Frame} {resume : Resume} {child : Evm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn callee resume pc')
    (enter : callee.enter = .run child)
    (installed : sem.At ca pc sevm pre) (foreign : sevm.currentTarget ≠ ca)
    (fork : CoveredFork sevm.benvStat.fork) :
    sem.At ca child.pc child.sta child.dyna ∧
      Devm.getStor child.dyna ca = Devm.getStor pre ca ∧
      (child.dyna.stack = [] ∧ child.dyna.memory = Mem.empty ∧ child.dyna.output = []) ∧
      child.sta.data.length < 2 ^ 256 ∧ child.sta.benvStat = sevm.benvStat ∧
      CoveredFork child.sta.benvStat.fork := by
  have nonempty : pre.getCode ca ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed.1, empty]
      rw [ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  obtain ⟨pcZero, codes, actualCode⟩ := Blanc.Evm.step_spawn_child step enter
  have childInstalled : sem.At ca child.pc child.sta child.dyna := by
    refine ⟨?_, ?_⟩
    · rw [codes]
      exact installed.1
    · intro target
      have away : sevm.currentTarget ≠ child.sta.currentTarget := by
        rw [target]
        exact foreign
      have codeEq : child.sta.code = pre.getCode ca := by
        rw [← target]
        exact actualCode away (by rw [target]; exact nonempty)
          (by rw [target]; exact sem.not_delegation installed.1)
      exact ⟨(congrArg (fun bytes : ByteArray => some bytes.toList) codeEq).trans
        installed.1, pcZero⟩
  have storageEq := (Blanc.Evm.step_spawn_child_world fork step enter nonempty).1
  obtain ⟨short, childFork⟩ := Blanc.ExecutionTrace.Evm.step_spawn_child_data fork step enter
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  have statEq : child.sta.benvStat = sevm.benvStat :=
    (Jaune.Frame.enter_run_benvStat enter).trans (Xinst.step_spawn_benvStat spawn)
  refine ⟨childInstalled, storageEq, ?_, short, statEq, childFork⟩
  refine ⟨?_, ?_, Blanc.Frame.enter_run_output_empty enter⟩
  · obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv enter
    rfl
  · obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv enter
    rfl

/-- A lifted instruction step, with its actual child if any, keeps every nonempty code. -/
theorem Lift.StepIn.codePreserve {R : Exec.Deriv} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (step : Lift.StepIn R sevm pre n post) : Devm.CodePreserve pre post := by
  obtain ⟨xl, inRoots, pc, run⟩ := step
  cases xl with
  | none => exact Ninst.codePreserve_effectRec (xl := .none) n trivial run
  | some slot =>
    obtain ⟨child, raw⟩ := slot
    obtain ⟨childRun, _⟩ := inRoots
    exact Ninst.codePreserve_effectRec (xl := .some ⟨child, raw⟩) n
      (Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
        Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect
        childRun) run

/-- A clean committed call-frame body survives settlement unchanged. -/
theorem Frame.ofCall_settle_clean {msg : Msg} {child : Devm} (clean : child.error = none) :
    (Frame.ofCall msg).settle (.ok child) = .ok child := by
  simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, executeCode.handleErrorWith_ok,
    processMessage.settle, Bind.bind, Except.bind, clean, Option.isSome_none,
    Bool.false_eq_true, ite_false]

/-- A successful CALL or STATICCALL step appends exactly its entered child's committed logs
when the child commits, and nothing otherwise (no child, or a rolled-back child). -/
theorem Xinst.call_run_logs {sevm : Sevm} {pre post : Devm} {x : Xinst} {xl : Xlot}
    (fork : CoveredFork sevm.benvStat.fork) (callFamily : x = .call ∨ x = .staticcall)
    (run : Xinst.Run sevm pre x xl (.ok post)) :
    (xl = .none → post.logs = pre.logs) ∧
    ∀ (child : Evm) (raw : Execution), xl = .some ⟨child, raw⟩ →
      (∀ committed : Execution.commits raw = true,
        post.logs = pre.logs ++ (Execution.committedPost raw committed).logs) ∧
      (¬ Execution.commits raw = true → post.logs = pre.logs) := by
  unfold Xinst.Run at run
  rcases Lift.Xinst.step_shapeLogs sevm pre x fork with ⟨ex, shape, logs⟩ |
    ⟨creates, d, e, na, mi, ms, logs, shape⟩ |
    ⟨d, g, v, c, t, ca, stv, isSt, ii, isz, oi, osz, code, dp, logs, shape⟩ <;>
    rw [shape] at run
  · obtain ⟨none, outEq⟩ := run
    subst outEq
    refine ⟨fun _ => logs.symm, ?_⟩
    intro child raw slot
    rw [none] at slot
    cases slot
  · exfalso
    rcases callFamily with rfl | rfl <;> rcases creates with h | h <;> cases h
  · refine ⟨fun none => ?_, ?_⟩
    · subst none
      exact (Lift.GenericCall.logs_of_ok fork.rules_stateGas_none run trivial).trans logs
    · intro child raw slot
      subst slot
      unfold genericCall.step at run
      split at run
      · rcases pushed : ((d.withReturnData []).withGasLeft ((d.withReturnData []).gasLeft + g)).push 0
          with failure | pushedDevm <;>
          simp only [pushed, XStep.ofExcept, bind, Except.bind, XStep.Run] at run
        · cases run.2
        · cases run.1
      · obtain ⟨settled, frameRun, resumed⟩ := run
        rcases settled with failure | settledChild
        · exact (Resume.call_run_error resumed.symm).elim
        have callLogs := Resume.call_logs resumed.symm
        have settledEq := (RunFrame.some_inv frameRun).2
        refine ⟨?_, ?_⟩
        · intro committed
          cases raw with
          | error failure => simp only [Execution.commits, Bool.false_eq_true] at committed
          | ok body =>
            have clean : body.error = none := by
              cases bodyError : body.error with
              | none => rfl
              | some reason =>
                simp only [Execution.commits, bodyError, Option.isNone_some,
                  Bool.false_eq_true] at committed
            rw [Frame.ofCall_settle_clean clean] at settledEq
            cases settledEq
            have notError : ¬ settledChild.error.isSome = true := by
              rw [clean]
              exact Bool.false_ne_true
            rw [ite_eq_right notError] at callLogs
            rw [callLogs, ← logs]
            rfl
        · intro rolled
          by_cases error : settledChild.error.isSome = true
          · rw [ite_eq_left error] at callLogs
            rw [callLogs, ← logs]
            rfl
          · have clean : settledChild.error.isSome = false := by
              cases flag : settledChild.error.isSome with
              | false => rfl
              | true => exact (error flag).elim
            exact (rolled (Frame.raw_commits_of_settlementCommits
              (ProcessMessage.settlementCommits_of_some_ok_clean frameRun clean))).elim

/-- The callee of a CALL or STATICCALL spawn is a message-call frame. -/
theorem Xinst.call_spawn_ofCall {sevm : Sevm} {pre : Devm} {x : Xinst}
    {callee : Jaune.Frame} {resume : Resume}
    (fork : CoveredFork sevm.benvStat.fork) (callFamily : x = .call ∨ x = .staticcall)
    (spawn : Xinst.step sevm pre x = .spawn callee resume) :
    ∃ msg, callee = Frame.ofCall msg := by
  rcases Lift.Xinst.step_shapeLogs sevm pre x fork with ⟨ex, shape, _⟩ |
    ⟨creates, d, e, na, mi, ms, _, shape⟩ |
    ⟨d, g, v, c, t, ca, stv, isSt, ii, isz, oi, osz, code, dp, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · exfalso
    rcases callFamily with rfl | rfl <;> rcases creates with h | h <;> cases h
  · unfold genericCall.step at spawn
    split at spawn
    · rcases pushed : ((d.withReturnData []).withGasLeft ((d.withReturnData []).gasLeft + g)).push 0
        with failure | pushedDevm <;>
        simp only [pushed, XStep.ofExcept, bind, Except.bind, reduceCtorEq] at spawn
      cases spawn
    · exact ⟨_, (XStep.spawn.inj spawn).1.symm⟩

/-- A child entered by an executable instruction starts with no logs. -/
theorem Xinst.spawn_child_logs {sevm : Sevm} {pre : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume} {child : Evm}
    (fork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (entered : frame.enter = .run child) : child.dyna.logs = [] := by
  obtain ⟨benv, transfer, rfl⟩ := Jaune.Frame.enter_run_inv entered
  apply Lift.initDevm_logs
  change benv.stat.rules.stateGas = none
  rw [benvAfterTransfer_stat transfer, Xinst.step_spawn_benvStat spawn]
  exact fork.rules_stateGas_none

/-- A CALL or STATICCALL step whose pushed success flag is nonzero committed its entered
child. -/
theorem Xinst.call_run_flag_commits {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {child : Evm} {raw : Execution}
    (fork : CoveredFork sevm.benvStat.fork) (callFamily : x = .call ∨ x = .staticcall)
    (run : Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok post))
    (flag : ∃ f rest, post.stack = f :: rest ∧ f ≠ 0) : Execution.commits raw = true := by
  unfold Xinst.Run at run
  rcases Lift.Xinst.step_shapeLogs sevm pre x fork with ⟨ex, shape, _⟩ |
    ⟨creates, d, e, na, mi, ms, _, shape⟩ |
    ⟨d, g, v, c, t, ca, stv, isSt, ii, isz, oi, osz, code, dp, _, shape⟩ <;>
    rw [shape] at run
  · cases run.1
  · exfalso
    rcases callFamily with rfl | rfl <;> rcases creates with h | h <;> cases h
  · unfold genericCall.step at run
    split at run
    · rcases pushed : ((d.withReturnData []).withGasLeft ((d.withReturnData []).gasLeft + g)).push 0
        with failure | pushedDevm <;>
        simp only [pushed, XStep.ofExcept, bind, Except.bind, XStep.Run] at run
      · cases run.2
      · cases run.1
    · obtain ⟨settled, frameRun, resumed⟩ := run
      rcases settled with failure | settledChild
      · exact (Resume.call_run_error resumed.symm).elim
      have stack := Resume.call_stack_flag resumed.symm
      obtain ⟨f, rest, flagStack, nonzero⟩ := flag
      have clean : settledChild.error.isSome = false := by
        cases error : settledChild.error.isSome with
        | false => rfl
        | true =>
          rw [error, ite_eq_left rfl, flagStack] at stack
          exact (nonzero (List.cons.inj stack).1).elim
      exact Frame.raw_commits_of_settlementCommits
        (ProcessMessage.settlementCommits_of_some_ok_clean frameRun clean)

/-- Code-free entry routes the message's code address to an enabled precompile. -/
theorem executeCode.enter_inr {m : Msg} {raw : Execution}
    (entry : executeCode.enter m = .inr raw) :
    ∃ adr, m.codeAddress = some adr ∧ m.disablePrecompiles = false ∧
      m.benv.stat.rules.isPrecomp adr := by
  unfold executeCode.enter at entry
  cases hca : m.codeAddress with
  | none =>
    simp only [hca, reduceCtorEq] at entry
  | some adr =>
    simp only [hca] at entry
    by_cases routed : (!m.disablePrecompiles && decide (m.benv.stat.rules.isPrecomp adr)) = true
    · rw [ite_eq_left routed] at entry
      obtain ⟨enabled, precomp⟩ := Bool.and_eq_true_iff.mp routed
      refine ⟨adr, rfl, ?_, of_decide_eq_true precomp⟩
      simpa only [Bool.not_eq_true'] using enabled
    · rw [ite_eq_right routed] at entry
      cases entry

/-- A childless processed call message with resolved, enabled routing reaches a
precompile at the original target. CALL and STATICCALL share this entry argument. -/
private theorem callMsg_none_precompile {sevm : Sevm} {parent child : Devm}
    {gas : Nat} {value : B256} {caller target actual : Adr} {static : Bool}
    {input : Bytes} {code : ByteArray} {dp : Bool}
    (routing : (actual = target ∧ dp = false) ∨ dp = true)
    (process : ProcessMessage
      (callMsg sevm parent gas value caller target actual true static input code dp)
      .none (.ok child)) :
    sevm.benvStat.rules.isPrecomp target := by
  unfold ProcessMessage RunFrame at process
  cases entered : (Frame.ofCall
      (callMsg sevm parent gas value caller target actual true static input code dp)).enter with
  | run evm =>
    rw [entered] at process
    obtain ⟨_, slot, _⟩ := process
    cases slot
  | done result =>
    rw [entered] at process
    obtain ⟨_, resultEq⟩ := process
    unfold Jaune.Frame.enter at entered
    split at entered
    · cases entered
      simp only [Frame.settleMsg, Frame.ofCall, processMessage.settle, bind, Except.bind,
        Bool.false_eq_true, ite_false, reduceCtorEq] at resultEq
    · rename_i benv transfer
      split at entered
      · cases entered
      · rename_i raw entry
        obtain ⟨adr, codeAddress, enabled, precomp⟩ := executeCode.enter_inr entry
        have stat : benv.stat = sevm.benvStat := benvAfterTransfer_stat transfer
        simp only [Msg.withBenv, Frame.ofCall, callMsg] at codeAddress enabled precomp
        rw [stat] at precomp
        rcases routing with ⟨nameEq, _⟩ | dpEq
        · subst nameEq
          cases codeAddress
          exact precomp
        · subst dpEq
          cases enabled

/-- A successful CALL step with a nonzero flag that enters no code frame ran the precompile
at its target: the target is a precompile of the fork and carries no delegation. -/
theorem Xinst.call_none_precompile {sevm : Sevm} {s sf : Devm}
    {g c v ii is oi os : B256} {xs : List B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (operands : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (run : Xinst.Run sevm s .call .none (.ok sf))
    (flag : ∃ f rest, sf.stack = f :: rest ∧ f ≠ 0) :
    sevm.benvStat.rules.isPrecomp c.toAdr := by
  have stepRun : ∀ pc, Ninst.StepRun pc sevm s Ninst.call .none (.ok sf) := by
    intro pc
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
    exact run
  rcases of_run_call_val_with_depth_frame operands ⟨.none, trivial, 0, stepRun 0⟩ fork with
    ⟨failed, _⟩ | ⟨parent, child, xl, dp, na, code, avail, pc, step, _, _, _, _, _, _, routing,
      filled, process, _, _, _, _, _, _⟩
  · obtain ⟨f, rest, flagStack, nonzero⟩ := flag
    rw [flagStack] at failed
    exact (nonzero (pref_head_unique failed (pref_append [f] rest)).symm).elim
  · obtain ⟨slotEq, _⟩ := Step.Run.unique_of_filled (show Xlot.Filled .none from trivial) filled (stepRun pc) step
    subst slotEq
    apply callMsg_none_precompile (process := process)
    rcases routing with ⟨_, nameEq, _, dpEq⟩ | ⟨_, _, _, _, dpEq⟩
    · exact Or.inl ⟨nameEq, dpEq⟩
    · exact Or.inr dpEq

/-- A successful STATICCALL with a nonzero flag and no interpreted child ran
an enabled precompile at its target. The inversion preserves the supplied empty slot. -/
theorem Xinst.staticcall_none_precompile {sevm : Sevm} {s sf : Devm}
    {g t ii is oi os : B256} {xs : List B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (operands : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (run : Xinst.Run sevm s .staticcall .none (.ok sf))
    (flag : ∃ f rest, sf.stack = f :: rest ∧ f ≠ 0) :
    sevm.benvStat.rules.isPrecomp t.toAdr := by
  have stepRun : Ninst.StepRun 0 sevm s Ninst.staticcall .none (.ok sf) := by
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
    exact run
  rcases of_step_staticcall_val_with_depth_frame_cause operands
      (show Xlot.Filled .none from trivial) stepRun fork with
    ⟨failed, _⟩ | ⟨parent, child, dp, na, code, avail, _, _, _, _, _, _, routing,
      _, process, _⟩
  · obtain ⟨f, rest, flagStack, nonzero⟩ := flag
    rw [flagStack] at failed
    exact (nonzero (pref_head_unique failed (pref_append [f] rest)).symm).elim
  · apply callMsg_none_precompile (process := process)
    rcases routing with ⟨_, nameEq, _, dpEq⟩ | ⟨_, _, _, _, dpEq⟩
    · exact Or.inl ⟨nameEq, dpEq⟩
    · exact Or.inr dpEq

end Blanc
