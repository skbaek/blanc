import Blanc.ExecutionTraceCallerExclusion
import Blanc.ExecutionTraceSettledFrames

/-!
# Empty code and caller exclusion from settled frames alone (retention probe)

Disposable probe, not a landing candidate. Everything here restates the empty-code route of
`ExecutionCodeAt`, `ExecutionTraceCodeAt`, `ExecutionCallerExclusion` and
`ExecutionTraceCallerExclusion` with its CREATE-avoidance premise ranging over settled frames
only. A rolled-back child restores the code at every address, so nothing a reverted subtree
does reaches a retained frame: no statement below names a reverted frame.
-/

namespace Blanc

open Jaune

/-! ## A rolled-back settlement restores code -/

/-- A call frame whose settlement succeeded without committing restored its entry code. -/
theorem Frame.ofCall_settle_rolledBack_getCode {msg : Msg} {raw : Execution} {post : Devm}
    (settled : (Frame.ofCall msg).settle raw = .ok post)
    (rolled : ¬ Frame.settlementCommits (Frame.ofCall msg) raw = true) (a : Adr) :
    post.getCode a = msg.benv.state.getCode a := by
  have dirty : post.error.isNone ≠ true := by
    intro clean
    apply rolled
    unfold Frame.settlementCommits
    rw [settled]
    exact clean
  have settled' : processMessage.settle msg
      (executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw) = .ok post := settled
  obtain ⟨evm, _, cases⟩ := processMessage.settle_ok_cases settled'
  rcases cases with ⟨_, rfl⟩ | ⟨notError, rfl⟩
  · exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a
  · exfalso
    apply dirty
    change evm.error.isNone = true
    cases error : evm.error with
    | none => rfl
    | some reason => simp only [error, Option.isSome_some, not_true_eq_false] at notError

/-- A CREATE frame whose settlement succeeded without committing restored its entry code. -/
theorem Frame.ofCreate_settle_rolledBack_getCode {msg : Msg} {raw : Execution} {post : Devm}
    (settled : (Frame.ofCreate msg).settle raw = .ok post)
    (rolled : ¬ Frame.settlementCommits (Frame.ofCreate msg) raw = true) (a : Adr) :
    post.getCode a = msg.benv.state.getCode a := by
  have dirty : post.error.isNone ≠ true := by
    intro clean
    apply rolled
    unfold Frame.settlementCommits
    rw [settled]
    exact clean
  have settled' : processCreateMessage.settle msg
      (processMessage.settle (processCreateMessage.msg msg)
        (executeCode.handleErrorWith (processCreateMessage.msg msg).benv.stat.rules.stateGas raw)) =
      .ok post := settled
  generalize processMessage.settle _ _ = inner at settled'
  cases inner with
  | error failure => exact absurd settled' (by
      rw [processCreateMessage.settle_error]
      simp only [reduceCtorEq, not_false_eq_true])
  | ok evm =>
    unfold processCreateMessage.settle at settled'
    dsimp only [bind, Except.bind] at settled'
    split at settled'
    · rename_i clean
      cases charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | ok charged =>
        rw [charge] at settled'
        cases settled'
        exfalso
        apply dirty
        change charged.error.isNone = true
        rw [processCreateMessage.chargeCodeGas_error_eq charge]
        exact clean
      | error failure =>
        rcases failure with ⟨reason, failed⟩
        rw [charge] at settled'
        cases reason <;> dsimp only at settled' <;> try cases settled'
        split <;> rfl
    · cases settled'
      exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a

/-- A spawned child that entered and rolled back leaves the parent's code as it was, whatever
its subtree did. -/
theorem Evm.step_spawn_rolledBack_getCode_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (resumed : resume.run (frame.settle raw) = .ok post)
    (rolled : ¬ Frame.settlementCommits frame raw = true) (a : Adr) :
    post.getCode a = pre.getCode a := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
    cases settled : (Frame.ofCreate _).settle raw with
    | error failure =>
      rcases failure with ⟨reason, state, created, transient⟩
      rw [settled] at resumed
      cases resumed
    | ok child =>
      rw [settled] at resumed
      have kept := Resume.create_getCode (a := a)
        (parent := addAccessedAddress
          (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress) (newAddress := newAddress)
        (r := .ok child) (Frame.ofCreate_settle_rolledBack_getCode settled rolled a)
      rw [resumed] at kept
      exact kept.trans ((addAccessedAddress_getCode ..).trans
        (Devm.incrNonce_getCode.trans (hprefix.getCode a).symm))
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    cases settled : (Frame.ofCall _).settle raw with
    | error failure =>
      rcases failure with ⟨reason, state, created, transient⟩
      rw [settled] at resumed
      cases resumed
    | ok child =>
      rw [settled] at resumed
      have kept := Resume.call_getCode (a := a) (parent := d.withReturnData [])
        (outputIndex := oi) (outputSize := osz)
        (r := .ok child) (Frame.ofCall_settle_rolledBack_getCode settled rolled a)
      rw [resumed] at kept
      exact kept.trans (hprefix.getCode a).symm

/-! ## Retained induction -/

/-- The induction on committing executions: a rolled-back child contributes nothing but its
parent's resumption, and the two failing constructors cannot occur. -/
theorem Exec.retained_induction
    {P : (pc : Nat) → (sevm : Sevm) → (pre : Devm) → (out : Execution) →
      Exec pc sevm pre out → Prop}
    (halt : ∀ {pc sevm pre out} (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out),
      P pc sevm pre out (.halt step))
    (cont : ∀ {pc sevm pre pc' post out} (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out), P pc' sevm post out next →
        P pc sevm pre out (.cont step next))
    (doneOk : ∀ {pc sevm pre frame resume pc' result post out}
      (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (enter : frame.enter = .done result) (resumed : resume.run result = .ok post)
      (next : Exec pc' sevm post out), P pc' sevm post out next →
        P pc sevm pre out (.doneOk step enter resumed next))
    (settled : ∀ {pc sevm pre frame resume pc' childEvm raw post out}
      (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (enter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (resumed : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out),
      Frame.settlementCommits frame raw = true →
      P childEvm.pc childEvm.sta childEvm.dyna raw child → P pc' sevm post out next →
        P pc sevm pre out (.runOk step enter child resumed next))
    (rolled : ∀ {pc sevm pre frame resume pc' childEvm raw post out}
      (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (enter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (resumed : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out),
      ¬ Frame.settlementCommits frame raw = true → P pc' sevm post out next →
        P pc sevm pre out (.runOk step enter child resumed next))
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    P pc sevm pre out run := by
  induction run with
  | halt step => exact halt step
  | cont step next ih => exact cont step next (ih committed)
  | doneErr step enter resumed =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resumed next ih => exact doneOk step enter resumed next (ih committed)
  | runErr step enter child resumed ih =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next
      childIH nextIH =>
    by_cases settles : Frame.settlementCommits frame raw = true
    · exact settled step enter child resumed next settles
        (childIH (Frame.raw_commits_of_settlementCommits settles)) (nextIH committed)
    · exact rolled step enter child resumed next settles (nextIH committed)

/-! ## Code and callers along one committing execution -/

namespace ExecutionTrace

/-- One entered, settling child keeps the code at `a` across its spawning step. -/
theorem Evm.step_spawn_settled_codeAt_noStateGas {a : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Jaune.Frame} {resume : Resume}
    {childEvm : Evm} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run childEvm)
    (child : Execution.Rel (Devm.CodeAt a) childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (avoid : childEvm.sta.codeAddress = none → childEvm.sta.currentTarget ≠ a) :
    Devm.CodeAt a pre post := by
  have codeAddress : childEvm.sta.codeAddress = frame.inner.codeAddress :=
    Frame.enter_run_codeAddress enter
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  exact Evm.step_codeAt_noStateGas (xl := .some ⟨_, _⟩) (out := .ok _) hsg
    (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
      rw [step] at h; cases h; rw [enter] at hen; cases hen
      rw [← Frame.enter_run_currentTarget enter]
      exact avoid (codeAddress.trans (Xinst.step_spawn_create_codeAddress_noStateGas hsg spawn hcr))))
    child (by rw [step]; exact ⟨_, RunFrame.of_run enter, resumed.symm⟩)

/-- A committing execution keeps the code at `a` when no retained frame below it is a CREATE at
`a`. CREATE frames in rolled-back subtrees are unconstrained. -/
theorem Exec.codeAt_retained_noStateGas {a : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (avoid : ∀ frame ∈ Exec.descendantFrames run,
      frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) :
    Execution.Rel (Devm.CodeAt a) pre out := by
  revert hsg avoid
  refine Exec.retained_induction
    (P := fun _ sevm pre out run => sevm.benvStat.rules.stateGas = none →
      (∀ frame ∈ Exec.descendantFrames run,
        frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) →
      Execution.Rel (Devm.CodeAt a) pre out)
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step hsg _
    exact Evm.step_codeAt_noStateGas (a := a) (xl := .none) hsg
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
  · intro pc sevm pre pc' post out step next ih hsg avoid
    have here : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _) hsg
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here
      (ih hsg (by simpa only [Exec.descendantFrames] using avoid))
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih hsg avoid
    have here : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _) hsg
      (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
        rw [step] at h; cases h; rw [enter] at hen; cases hen))
      trivial (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here
      (ih hsg (by simpa only [Exec.descendantFrames] using avoid))
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next
      settles childIH nextIH hsg avoid
    rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next settles]
      at avoid
    have childHsg : childEvm.sta.benvStat.rules.stateGas = none := by
      rw [Evm.step_spawn_child_benvStat step enter]
      exact hsg
    have here := Evm.step_spawn_settled_codeAt_noStateGas hsg step enter
      (childIH childHsg (fun f member => avoid f (List.mem_cons_of_mem _
        (List.mem_append_left _ member)))) resumed
      (avoid _ List.mem_cons_self)
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here
      (nextIH hsg (fun f member => avoid f (List.mem_cons_of_mem _
        (List.mem_append_right _ member))))
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next
      rolled nextIH hsg avoid
    rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next rolled]
      at avoid
    have here : Devm.CodeAt a pre post :=
      Evm.step_spawn_rolledBack_getCode_noStateGas hsg step resumed rolled a
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here (nextIH hsg avoid)

/-- Below a committing execution whose caller is not `a`, and which runs empty code if it is at
`a`, every retained frame has a caller other than `a` and runs empty code if it is at `a`. -/
theorem Exec.descendantFrames_caller_excluded_noStateGas {a : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (empty : pre.getCode a = ByteArray.empty)
    (avoid : ∀ frame ∈ Exec.descendantFrames run,
      frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) :
    ∀ frame ∈ Exec.descendantFrames run,
      frame.sevm.caller ≠ a ∧
        (frame.sevm.currentTarget = a → frame.sevm.code = ByteArray.empty) := by
  revert hsg caller targetCode empty avoid
  refine Exec.retained_induction
    (P := fun _ sevm pre _ run => sevm.benvStat.rules.stateGas = none →
      sevm.caller ≠ a → (sevm.currentTarget = a → sevm.code = ByteArray.empty) →
      pre.getCode a = ByteArray.empty →
      (∀ frame ∈ Exec.descendantFrames run,
        frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) →
      ∀ frame ∈ Exec.descendantFrames run,
        frame.sevm.caller ≠ a ∧
          (frame.sevm.currentTarget = a → frame.sevm.code = ByteArray.empty))
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _ _ _ _ _ frame member
    simp only [Exec.descendantFrames, List.not_mem_nil] at member
  · intro pc sevm pre pc' post out step next ih hsg caller targetCode empty avoid
    have here : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _) hsg
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    simpa only [Exec.descendantFrames] using ih hsg caller targetCode (here.trans empty)
      (by simpa only [Exec.descendantFrames] using avoid)
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih hsg caller
      targetCode empty avoid
    have here : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _) hsg
      (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
        rw [step] at h; cases h; rw [enter] at hen; cases hen))
      trivial (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
    simpa only [Exec.descendantFrames] using ih hsg caller targetCode (here.trans empty)
      (by simpa only [Exec.descendantFrames] using avoid)
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next
      settles childIH nextIH hsg caller targetCode empty avoid
    rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next settles]
      at avoid ⊢
    have childHsg : childEvm.sta.benvStat.rules.stateGas = none := by
      rw [Evm.step_spawn_child_benvStat step enter]
      exact hsg
    have childAvoid : ∀ f ∈ Exec.descendantFrames child,
        f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a := fun f member =>
      avoid f (List.mem_cons_of_mem _ (List.mem_append_left _ member))
    have rootAvoid := avoid _ List.mem_cons_self
    have childEmpty : childEvm.dyna.getCode a = ByteArray.empty :=
      ((Evm.step_spawn_child step enter).2.1 a).trans empty
    obtain ⟨childCaller, childCode⟩ := Evm.step_spawn_caller_excluded_noStateGas step hsg enter
      caller targetCode childEmpty rootAvoid
    have here := Evm.step_spawn_settled_codeAt_noStateGas hsg step enter
      (Exec.codeAt_retained_noStateGas child (Frame.raw_commits_of_settlementCommits settles)
        childHsg childAvoid) resumed rootAvoid
    have below := childIH childHsg childCaller childCode childEmpty childAvoid
    have after := nextIH hsg caller targetCode (here.trans empty) (fun f member =>
      avoid f (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
    intro f member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with (rfl | member) | member
    · exact ⟨childCaller, childCode⟩
    · exact below f member
    · exact after f member
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next
      rolled nextIH hsg caller targetCode empty avoid
    rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next rolled]
      at avoid ⊢
    exact nextIH hsg caller targetCode
      ((Evm.step_spawn_rolledBack_getCode_noStateGas hsg step resumed rolled a).trans empty) avoid

/-! ## Code through the message wrappers -/

/-- A settled message keeps the code at `a` when no settled frame of it is a CREATE at `a`. -/
theorem ProcessMessageTrace.codeAt_settled_noStateGas
    {a : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none)
    (avoid : ∀ frame ∈ trace.settledFrames,
      frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) :
    post.getCode a = msg.benv.state.getCode a := by
  obtain ⟨slot, retained, hrun⟩ := trace
  cases retained with
  | none => exact ProcessMessage.codeAt (a := a) (xl := .none) trivial hrun
  | @some pc sevm pre raw run =>
    obtain ⟨enter, settled⟩ := RunFrame.some_inv hrun
    by_cases settles : Frame.settlementCommits (Frame.ofCall msg) raw = true
    · have committed := Frame.raw_commits_of_settlementCommits settles
      simp only [ProcessMessageTrace.settledFrames, settles, ite_true, Exec.committedFrames,
        committed, dite_true] at avoid
      have rel := Exec.codeAt_retained_noStateGas run committed
        (by rw [Frame.enter_run_benvStat enter]; exact hsg)
        (fun frame member => avoid frame (List.mem_cons_of_mem _ member))
      exact ProcessMessage.codeAt (Xlot.invAt_of_rel (xl := .some ⟨⟨pc, sevm, pre⟩, raw⟩) rel) hrun
    · exact Frame.ofCall_settle_rolledBack_getCode settled.symm settles a

/-- A settled CREATE message keeps the code at `a` when no settled frame of it is a CREATE at
`a`; a rolled-back CREATE at `a` restores it. -/
theorem ProcessCreateMessageTrace.codeAt_settled_noStateGas
    {a : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none) (hca : msg.codeAddress = none)
    (avoid : ∀ frame ∈ trace.settledFrames,
      frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) :
    post.getCode a = msg.benv.state.getCode a := by
  obtain ⟨slot, retained, hrun⟩ := trace
  cases retained with
  | none => exact ProcessCreateMessage.codeAt_none hca hrun
  | @some pc sevm pre raw run =>
    obtain ⟨enter, settled⟩ := RunFrame.some_inv hrun
    by_cases settles : Frame.settlementCommits (Frame.ofCreate msg) raw = true
    · have committed := Frame.raw_commits_of_settlementCommits settles
      simp only [ProcessCreateMessageTrace.settledFrames, settles, ite_true, Exec.committedFrames,
        committed, dite_true] at avoid
      have rel := Exec.codeAt_retained_noStateGas run committed
        (by
          rw [Frame.enter_run_benvStat enter]
          change (processCreateMessage.msg msg).benv.stat.rules.stateGas = none
          rw [processCreateMessage.msg_benvStat]
          exact hsg)
        (fun frame member => avoid frame (List.mem_cons_of_mem _ member))
      have different : a ≠ msg.currentTarget := by
        intro same
        have root := avoid _ List.mem_cons_self
        exact root ((Frame.enter_run_codeAddress enter).trans hca)
          ((Frame.enter_run_currentTarget enter).trans same.symm)
      exact ProcessCreateMessage.codeAt different
        (Xlot.invAt_of_rel (xl := .some ⟨⟨pc, sevm, pre⟩, raw⟩) rel) hrun
    · exact Frame.ofCreate_settle_rolledBack_getCode settled.symm settles a

/-- A settled message call keeps the code at `a` when no settled frame of it is a CREATE at `a`
and no authorization of its transaction recovers to `a`. -/
theorem MessageCallTrace.codeAt_settled_noStateGas
    {a : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hca : msg.target.isNone = true → msg.codeAddress = none)
    (hauth : ∀ auth ∈ msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ frame ∈ trace.settledFrames,
      frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a) :
    state.getCode a = msg.benv.state.getCode a := by
  cases trace with
  | createCollision target collision result =>
    rw [processMessageCall_createCollision_state_eq_noStateGas target collision result hsg]
  | createRun target collision evm core coreTrace result =>
    rw [processMessageCall_createRun_state_eq_noStateGas target collision core result hsg]
    exact coreTrace.codeAt_settled_noStateGas hsg (hca target) avoid
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    have hsgExec : execMsg.benv.stat.rules.stateGas = none := by
      rw [execMsgEq, messageCallExecutionMessage_benv_stat,
        messageCallDelegation_benv_stat delegation]
      exact hsg
    have hcode : execMsg.benv.state.getCode a = msg.benv.state.getCode a := by
      rw [execMsgEq, messageCallExecutionMessage_getCode]
      exact messageCallDelegation_getCode hauth delegation
    rw [processMessageCall_callRun_state_eq_noStateGas target delegation execMsgEq core result hsg]
    exact (coreTrace.codeAt_settled_noStateGas hsgExec avoid).trans hcode

/-- A transaction that starts with empty code at `a` ends with it, when no settled frame of it
is a CREATE at `a` and no authorization of it recovers to `a`. -/
theorem TransactionTrace.codeAt_empty_settled_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {a : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hauth : ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ frame ∈ trace.settledFrames,
      frame.sevm.codeAddress = none → frame.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    state.getCode a = ByteArray.empty := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode a = ByteArray.empty := by
    rw [hbenv]
    exact hdebit.trans hempty
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hmsgAuth : ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a := by
    rw [htenv]
    simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth
  have hpost := trace.message.codeAt_settled_noStateGas hmsgSg hca hmsgAuth avoid
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_selectedFinalStateForm hsg
  rw [hfinal, sweepTouchedAccounts_getCode_empty _ _ (foldl_destroyAccount_getCode_empty _ (by
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hpost.trans hmsgState))]

/-! ## Callers through the message wrappers -/

/-- Private in `ExecutionTraceCallerExclusion`; restated because existing modules stay untouched. -/
private theorem messageCallDelegation_code_own
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (address : msg.codeAddress = some msg.currentTarget)
    (code : msg.code = msg.benv.state.getCode msg.currentTarget) :
    delegated.code = delegated.benv.state.getCode delegated.currentTarget := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    exact code
  · obtain ⟨⟨middle, counter⟩, delegation, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, _⟩
    unfold setDelegation at delegation
    obtain ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩ := Except.bind_eq_ok delegation
    have fields := setDelegationLoop_fields loop
    have loopAddress : loopMsg.codeAddress = some loopMsg.currentTarget := by
      rw [fields.2.2.2.2.2, address, fields.2.2.1]
    simp only [loopAddress, Bind.bind, Except.bind,
      Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, _⟩
    rfl

/-- The caller exclusion for a retained slot, from its entry alone. -/
theorem RetainedXlot.settled_caller_excluded
    {frame : Jaune.Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (retained : RetainedXlot slot) (run : RunFrame frame slot out)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    (caller : frame.inner.caller ≠ a)
    (code : frame.inner.codeAddress = Option.none ∨
      (frame.inner.currentTarget = a → frame.inner.code = ByteArray.empty))
    (empty : frame.inner.benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ f ∈ retained.settledFrames,
      f.sevm.codeAddress = Option.none → f.sevm.currentTarget ≠ a) :
    ∀ f ∈ retained.settledFrames, f.sevm.caller ≠ a := by
  cases retained with
  | none => intro f member; simp only [RetainedXlot.settledFrames, List.not_mem_nil] at member
  | @some pc sevm pre raw execution =>
    by_cases committed : Execution.commits raw = true
    · simp only [RetainedXlot.settledFrames, Exec.committedFrames, committed, dite_true]
        at avoid ⊢
      have enter := (RunFrame.some_inv run).1
      have rootSg : sevm.benvStat.rules.stateGas = Option.none := by
        rw [Frame.enter_run_benvStat enter]
        exact hsg
      have rootCaller : sevm.caller ≠ a := by
        rw [Frame.enter_run_caller enter]
        exact caller
      have rootCode : sevm.currentTarget = a → sevm.code = ByteArray.empty := by
        intro target
        rcases code with create | own
        · exact False.elim (avoid _ List.mem_cons_self
            ((Frame.enter_run_codeAddress enter).trans create) target)
        · rw [Frame.enter_run_code enter]
          exact own ((Frame.enter_run_currentTarget enter).symm.trans target)
      have below := Exec.descendantFrames_caller_excluded_noStateGas execution committed rootSg
        rootCaller rootCode ((Frame.enter_run_getCode enter a).trans empty)
        (fun f member => avoid f (List.mem_cons_of_mem _ member))
      intro f member
      rcases List.mem_cons.mp member with rfl | member
      · exact rootCaller
      · exact (below f member).1
    · intro f member
      simp only [RetainedXlot.settledFrames, Exec.committedFrames, committed,
        Bool.false_eq_true, ↓reduceDIte, List.not_mem_nil] at member

theorem ProcessMessageTrace.settledFrames_cases {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (trace : ProcessMessageTrace msg out) :
    trace.settledFrames = [] ∨ trace.settledFrames = trace.retained.settledFrames := by
  obtain ⟨slot, retained, run⟩ := trace
  cases retained with
  | none => exact Or.inl rfl
  | @some pc sevm pre raw execution =>
    by_cases settles : Frame.settlementCommits (Frame.ofCall msg) raw = true
    · exact Or.inr (by simp only [ProcessMessageTrace.settledFrames, settles, ite_true,
        RetainedXlot.settledFrames])
    · exact Or.inl (by simp only [ProcessMessageTrace.settledFrames, settles, Bool.false_eq_true, ↓reduceIte])

theorem ProcessCreateMessageTrace.settledFrames_cases {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    trace.settledFrames = [] ∨ trace.settledFrames = trace.retained.settledFrames := by
  obtain ⟨slot, retained, run⟩ := trace
  cases retained with
  | none => exact Or.inl rfl
  | @some pc sevm pre raw execution =>
    by_cases settles : Frame.settlementCommits (Frame.ofCreate msg) raw = true
    · exact Or.inr (by simp only [ProcessCreateMessageTrace.settledFrames, settles, ite_true,
        RetainedXlot.settledFrames])
    · exact Or.inl (by simp only [ProcessCreateMessageTrace.settledFrames, settles, Bool.false_eq_true, ↓reduceIte])

/-- Every settled frame of a message call has a caller other than `a`. -/
theorem MessageCallTrace.settled_caller_excluded
    {msg : Msg} {state : State} {out : MsgCallOutput} {a : Adr}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = Option.none) (caller : msg.caller ≠ a)
    (createAddress : msg.target.isNone = true → msg.codeAddress = none)
    (callCode : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (hauth : ∀ auth ∈ msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (empty : msg.benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ f ∈ trace.settledFrames,
      f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a) :
    ∀ f ∈ trace.settledFrames, f.sevm.caller ≠ a := by
  cases trace with
  | createCollision =>
    intro f member
    simp only [MessageCallTrace.settledFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
    simp only [MessageCallTrace.settledFrames] at avoid ⊢
    rcases coreTrace.settledFrames_cases with none | same
    · intro f member
      rw [none] at member
      exact False.elim (List.not_mem_nil member)
    · rw [same] at avoid ⊢
      exact RetainedXlot.settled_caller_excluded coreTrace.retained coreTrace.run
        (by change (processCreateMessage.msg msg).benv.stat.rules.stateGas = Option.none
            rw [processCreateMessage.msg_benvStat]; exact hsg)
        caller (Or.inl (createAddress target))
        ((processCreateMessage.msg_getCode msg a).trans empty) avoid
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    simp only [MessageCallTrace.settledFrames] at avoid ⊢
    subst execMsgEq
    have hcode : (messageCallExecutionMessage delegated).benv.state.getCode a =
        msg.benv.state.getCode a := by
      rw [messageCallExecutionMessage_getCode]
      exact messageCallDelegation_getCode hauth delegation
    have own := messageCallDelegation_code_own delegation
      (callCode target).1 (callCode target).2
    rcases coreTrace.settledFrames_cases with none | same
    · intro f member
      rw [none] at member
      exact False.elim (List.not_mem_nil member)
    · rw [same] at avoid ⊢
      exact RetainedXlot.settled_caller_excluded coreTrace.retained coreTrace.run
        (by change (messageCallExecutionMessage delegated).benv.stat.rules.stateGas = Option.none
            rw [messageCallExecutionMessage_benv_stat,
              messageCallDelegation_benv_stat delegation]; exact hsg)
        (by change (messageCallExecutionMessage delegated).caller ≠ a
            rw [messageCallExecutionMessage_caller_eq,
              messageCallDelegation_caller_eq delegation]; exact caller)
        (Or.inr (messageCallExecutionMessage_code_empty own
          (by rw [← messageCallExecutionMessage_getCode delegated a]; exact hcode.trans empty)))
        (hcode.trans empty) avoid

/-- Every settled frame of a transaction starting with empty code at `a` has a caller other
than `a`. -/
theorem TransactionTrace.settled_caller_excluded_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {a : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = Option.none) (sender : trace.sender ≠ a)
    (hauth : ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ f ∈ trace.settledFrames, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    ∀ f ∈ trace.settledFrames, f.sevm.caller ≠ a := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgAuth : ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a := by
    rw [htenv]
    simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth
  have callCode : trace.msg.target.isNone = false →
      trace.msg.codeAddress = some trace.msg.currentTarget ∧
        trace.msg.code = trace.msg.benv.state.getCode trace.msg.currentTarget :=
    prepareMessage_callCode trace.prepared
  exact trace.message.settled_caller_excluded
    (by rw [hbenv]; exact hsg)
    (by rw [trace.msg_caller]; exact sender)
    hca callCode hmsgAuth
    (by rw [hbenv]; exact hdebit.trans hempty) avoid

/-- A selected transaction list starting with empty code at `a` ends with it, and every settled
frame of it has a caller other than `a`. -/
theorem ApplyTransactionsTrace.settled_caller_excluded_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput} {a : Adr}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = Option.none) (senders : trace.NoSenderAt a)
    (hauth : ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ f ∈ trace.settledFrames, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ f ∈ trace.settledFrames, f.sevm.caller ≠ a) ∧
      finalBenv.state.getCode a = ByteArray.empty := by
  induction trace with
  | nil =>
    exact ⟨fun f member => by
      simp only [ApplyTransactionsTrace.settledFrames, List.not_mem_nil] at member, hempty⟩
  | cons head tail ih =>
    have headAvoid : ∀ f ∈ head.settledFrames,
        f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a :=
      fun f member => avoid f (List.mem_append_left _ member)
    have headAuth := hauth _ List.mem_cons_self
    have headEmpty := head.codeAt_empty_settled_noStateGas hsg headAuth headAvoid hempty
    have headCallers := head.settled_caller_excluded_noStateGas hsg senders.1 headAuth headAvoid
      hempty
    obtain ⟨tailCallers, final⟩ := ih hsg senders.2 (fun p member => hauth p (List.mem_cons_of_mem _ member))
      (fun f member => avoid f (List.mem_append_right _ member)) headEmpty
    refine ⟨fun f member => ?_, final⟩
    simp only [ApplyTransactionsTrace.settledFrames, List.mem_append] at member
    rcases member with member | member
    · exact headCallers f member
    · exact tailCallers f member

/-! ## Blocks and histories -/

/-- A system message keeps the code at `a` when no settled frame of it is a CREATE at `a`. -/
theorem SystemMessageTrace.codeAt_settled
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (avoid : ∀ f ∈ trace.settledFrames,
      f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a := by
  have hsg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    change benv.stat.rules.stateGas = none
    exact hfork.rules_stateGas_none
  have hca : (systemTransactionMessage benv target data).target.isNone = true →
      (systemTransactionMessage benv target data).codeAddress = none := by
    intro h
    simp only [systemTransactionMessage, processSystemTransactionMsg, Option.isNone_some,
      Bool.false_eq_true] at h
  have hauth : ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
    intro auth hauth
    simp only [systemTransactionMessage, processSystemTransactionMsg, processSystemTransactionTenv,
      Std.TreeMap.empty_eq_emptyc, List.not_mem_nil] at hauth
  exact trace.message.codeAt_settled_noStateGas hsg hca hauth avoid

theorem RequestsTrace.codeAt_settled
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (avoid : ∀ f ∈ trace.settledFrames,
      f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a := by
  have withdrawal := trace.withdrawal.codeAt_settled hfork (fun f member =>
    avoid f (List.mem_append_left _ member))
  have consolidation := trace.consolidation.codeAt_settled
    (benv := benv.withState trace.withdrawalState) hfork (fun f member =>
      avoid f (List.mem_append_right _ member))
  rw [trace.state_eq_consolidationState]
  exact consolidation.trans withdrawal

/-- A block body that starts with empty code at `a` ends with it, and each settled frame of its
transactions has a caller other than `a`, when no settled frame of the body is a CREATE at `a`
and no sender or authorization of its transactions is `a`. -/
theorem AppliedBodyTrace.settled_caller_excluded
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (senders : trace.transactions.NoSenderAt a)
    (hauth : ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ f ∈ trace.settledFrames,
      f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ f ∈ trace.transactions.settledFrames, f.sevm.caller ≠ a) ∧
      state.getCode a = ByteArray.empty := by
  have beacon := trace.beacon.codeAt_settled hfork (a := a) (fun f member => avoid f (by
    simp only [AppliedBodyTrace.settledFrames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl member))))
  have history := trace.history.codeAt_settled (benv := benv.withState trace.beaconState)
    hfork (a := a) (fun f member => avoid f (by
      simp only [AppliedBodyTrace.settledFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member))))
  have start : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode a =
      ByteArray.empty := history.trans (beacon.trans hempty)
  obtain ⟨callers, final⟩ := trace.transactions.settled_caller_excluded_noStateGas
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    hfork.rules_stateGas_none senders hauth
    (fun f member => avoid f (by
      simp only [AppliedBodyTrace.settledFrames, List.mem_append]
      exact Or.inl (Or.inr member))) start
  refine ⟨callers, ?_⟩
  have hfork' : CoveredFork
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)).stat.fork := by
    change CoveredFork trace.transactionBenv.stat.fork
    rw [trace.transactions.stat_eq]
    exact hfork
  have requests := trace.requests.codeAt_settled hfork' (a := a) (fun f member => avoid f (by
    simp only [AppliedBodyTrace.settledFrames, List.mem_append]
    exact Or.inr member))
  rw [← trace.requestState_eq, requests]
  change (processWithdrawalsState trace.transactionBenv.state wds).getCode a = _
  rw [processWithdrawalsState_getCode]
  exact final

/-- A configured history that starts with empty code at `a` ends with it, when no settled frame
is a CREATE at `a`, and no checked sender or authorization is `a`. -/
theorem ConfiguredHistoryTrace.codeAt_empty_settled
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {a : Adr}
    (senders : trace.NoSenderAt a) (hauth : trace.NoAuthorityAt a)
    (avoid : ∀ f ∈ trace.settledFrames,
      f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    future.state.getCode a = ByteArray.empty := by
  induction trace with
  | refl => exact hempty
  | step prior block ih =>
    have before := ih senders.1 hauth.1 (fun f member => avoid f (List.mem_append_left _ member))
    obtain ⟨-, state⟩ := block.bodyTrace.settled_caller_excluded
      (by change CoveredFork block.fork; exact block.covered) senders.2 hauth.2
      (fun f member => avoid f (List.mem_append_right _ member)) before
    rw [block.postState]
    exact state

/-- Every settled transaction frame of the last block of a history has a caller other than an
address that started empty, was never a sender or authority, and was never the target of a
settled CREATE. No reverted frame is constrained. -/
theorem ConfiguredHistoryTrace.block_settled_caller_excluded
    {cfg : ChainConfig} {checkpoint pre post : BlockChain} {a : Adr}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt a)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt a)
    (avoid : ∀ f ∈ (ConfiguredHistoryTrace.step history block).settledFrames,
      f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a)
    (initial : checkpoint.state.getCode a = ByteArray.empty) :
    ∀ frame ∈ block.bodyTrace.transactions.settledFrames, frame.sevm.caller ≠ a :=
  (block.bodyTrace.settled_caller_excluded
    (by change CoveredFork block.fork; exact block.covered) senders.2 authorities.2
    (fun f member => avoid f (List.mem_append_right _ member))
    (history.codeAt_empty_settled senders.1 authorities.1
      (fun f member => avoid f (List.mem_append_left _ member)) initial)).1

end ExecutionTrace

end Blanc
