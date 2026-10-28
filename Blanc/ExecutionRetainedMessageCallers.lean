import Blanc.ExecutionRetainedCodeAt
import Blanc.ExecutionTraceCallerExclusion
import Blanc.ExecutionTraceSettledFrames

/-!
# Empty-code caller exclusion through complete message settlement

Creation avoidance ranges over the actual settled frames. A discarded message
restores entry code and contributes no caller obligation, including a raw
constructor that fails code-deposit settlement. Initial code and admitted
sender exclusion remain separate premises.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual final error flag selects the retained call-message forest. -/
theorem ProcessMessageTrace.settledFrames_eq_if_clean {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post)) :
    trace.settledFrames = if post.error.isNone = true then trace.retained.settledFrames else [] := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => simp only [ProcessMessageTrace.settledFrames, RetainedXlot.settledFrames, ite_self]
  | some run =>
    simp only [ProcessMessageTrace.settledFrames, Frame.settlementCommits,
      ← (RunFrame.some_inv process).2, RetainedXlot.settledFrames]

/-- CREATE uses the complete settlement flag, including code deposit. -/
theorem ProcessCreateMessageTrace.settledFrames_eq_if_clean {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post)) :
    trace.settledFrames = if post.error.isNone = true then trace.retained.settledFrames else [] := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => simp only [ProcessCreateMessageTrace.settledFrames, RetainedXlot.settledFrames, ite_self]
  | some run =>
    simp only [ProcessCreateMessageTrace.settledFrames, Frame.settlementCommits,
      ← (RunFrame.some_inv process).2, RetainedXlot.settledFrames]

/-- A clean complete settlement lets the interpreter core use precisely the
retained forest; root code comes from actual frame entry. -/
theorem RetainedXlot.codeAt_callers_of_clean_runFrame
    {frame : Frame} {slot : Xlot} {post : Devm} {a : Adr}
    (retained : RetainedXlot slot) (process : RunFrame frame slot (.ok post))
    (clean : post.error.isNone = true)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    (caller : frame.inner.caller ≠ a)
    (code : frame.inner.codeAddress = Option.none ∨
      (frame.inner.currentTarget = a → frame.inner.code = ByteArray.empty))
    (initial : frame.inner.benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ retained.settledFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a) :
    Xlot.InvAt a slot ∧ ∀ root ∈ retained.settledFrames, root.sevm.caller ≠ a := by
  cases retained with
  | none => exact ⟨trivial, fun root member => (List.not_mem_nil member).elim⟩
  | @some pc sevm pre raw run =>
    obtain ⟨enter, settled⟩ := RunFrame.some_inv process
    have settles : frame.settlementCommits raw = true := by
      simp only [Frame.settlementCommits, ← settled, clean]
    have commits := Frame.raw_commits_of_settlementCommits settles
    have member : Exec.Frame.ofRun run commits ∈ (RetainedXlot.some run).settledFrames := by
      simp only [RetainedXlot.settledFrames, Exec.committedFrames, dite_eq_left commits]
      exact List.mem_cons_self
    have rootGas : sevm.benvStat.rules.stateGas = Option.none := by
      rw [Frame.enter_run_benvStat enter]; exact hsg
    have rootCaller : sevm.caller ≠ a := by
      rw [Frame.enter_run_caller enter]; exact caller
    have rootEmpty := (Frame.enter_run_getCode enter a).trans initial
    have rootCode : sevm.currentTarget = a → sevm.code = ByteArray.empty := by
      intro target
      rcases code with create | own
      · exact (avoid _ member ((Frame.enter_run_codeAddress enter).trans create) target).elim
      · rw [Frame.enter_run_code enter]
        exact own ((Frame.enter_run_currentTarget enter).symm.trans target)
    have descendantAvoid : ∀ root ∈ Exec.descendantFrames run,
        root.sevm.codeAddress = Option.none → root.sevm.currentTarget ≠ a := by
      intro root inChild
      apply avoid root
      simp only [RetainedXlot.settledFrames, Exec.committedFrames, dite_eq_left commits]
      exact List.mem_cons_of_mem _ inChild
    obtain ⟨last, callers⟩ := Exec.codeAt_and_callers_retained_noStateGas run commits
      rootGas rootCaller rootCode rootEmpty descendantAvoid
    refine ⟨?_, callers⟩
    cases raw with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at commits
    | ok result => exact (last.trans rootEmpty.symm).symm

/-- Calls preserve empty code and exclude callers using only retained
creation avoidance; a failed complete settlement restores the entry state. -/
theorem ProcessMessageTrace.codeAt_callers_retained_noStateGas
    {msg : Msg} {post : Devm} {a : Adr} (trace : ProcessMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = Option.none) (caller : msg.caller ≠ a)
    (own : msg.currentTarget = a → msg.code = ByteArray.empty)
    (initial : msg.benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.settledFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a) :
    post.getCode a = ByteArray.empty ∧ ∀ root ∈ trace.settledFrames, root.sevm.caller ≠ a := by
  rw [trace.settledFrames_eq_if_clean] at avoid ⊢
  by_cases clean : post.error.isNone = true
  · rw [ite_eq_left clean] at avoid ⊢
    obtain ⟨inv, callers⟩ := trace.retained.codeAt_callers_of_clean_runFrame trace.run clean
      hsg caller (Or.inr own) initial avoid
    exact ⟨(ProcessMessage.codeAt inv trace.run).trans initial, callers⟩
  · rw [ite_eq_right clean]
    have failed : post.error.isSome = true := by
      cases eq : post.error with
      | none => exact (clean (by rw [eq]; rfl)).elim
      | some error => rfl
    have rollback := (ProcessMessage.rollback_of_error trace.run failed).1
    exact ⟨(congrArg (fun state => state.getCode a) rollback).trans initial,
      fun root member => (List.not_mem_nil member).elim⟩

/-- CREATE may be discarded at any address. Only a retained constructor must
avoid `a`, and only its retained descendants impose further obligations. -/
theorem ProcessCreateMessageTrace.codeAt_callers_retained_noStateGas
    {msg : Msg} {post : Devm} {a : Adr} (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = Option.none) (caller : msg.caller ≠ a)
    (create : msg.codeAddress = Option.none)
    (initial : msg.benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.settledFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a) :
    post.getCode a = ByteArray.empty ∧ ∀ root ∈ trace.settledFrames, root.sevm.caller ≠ a := by
  rw [trace.settledFrames_eq_if_clean] at avoid ⊢
  by_cases clean : post.error.isNone = true
  · rw [ite_eq_left clean] at avoid ⊢
    have innerGas : (Frame.ofCreate msg).inner.benv.stat.rules.stateGas = Option.none := by
      change (processCreateMessage.msg msg).benv.stat.rules.stateGas = Option.none
      rw [processCreateMessage.msg_benvStat]; exact hsg
    have innerEmpty : (Frame.ofCreate msg).inner.benv.state.getCode a = ByteArray.empty :=
      (processCreateMessage.msg_getCode msg a).trans initial
    obtain ⟨inv, callers⟩ := trace.retained.codeAt_callers_of_clean_runFrame trace.run clean
      innerGas caller (Or.inl create) innerEmpty avoid
    refine ⟨?_, callers⟩
    rcases trace with ⟨slot, retained, process⟩
    cases retained with
    | none => exact (ProcessCreateMessage.codeAt_none create process).trans initial
    | @some pc sevm pre raw run =>
      obtain ⟨enter, settled⟩ := RunFrame.some_inv process
      have settles : (Frame.ofCreate msg).settlementCommits raw = true := by
        simp only [Frame.settlementCommits, ← settled, clean]
      have commits := Frame.raw_commits_of_settlementCommits settles
      have member : Exec.Frame.ofRun run commits ∈ (RetainedXlot.some run).settledFrames := by
        simp only [RetainedXlot.settledFrames, Exec.committedFrames, dite_eq_left commits]
        exact List.mem_cons_self
      have targetNe : a ≠ msg.currentTarget := by
        intro same
        exact avoid _ member ((Frame.enter_run_codeAddress enter).trans create)
          ((Frame.enter_run_currentTarget enter).trans same.symm)
      exact (ProcessCreateMessage.codeAt targetNe inv process).trans initial
  · rw [ite_eq_right clean]
    have failed : post.error.isSome = true := by
      cases eq : post.error with
      | none => exact (clean (by rw [eq]; rfl)).elim
      | some error => rfl
    have rollback := ProcessCreateMessage.rollback_of_error trace.run failed
    exact ⟨(congrArg (fun state => state.getCode a) rollback).trans initial,
      fun root member => (List.not_mem_nil member).elim⟩

/-- Before delegation is enabled, the exact message wrapper supplies caller
and code provenance without authority queries or discarded-frame restrictions. -/
theorem MessageCallTrace.codeAt_callers_retained_of_disabled
    {msg : Msg} {state : State} {out : MsgCallOutput} {a : Adr}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (delegationDisabled : msg.benv.stat.rules.delegationEnabled = false)
    (caller : msg.caller ≠ a)
    (createAddress : msg.target.isNone = true → msg.codeAddress = none)
    (callCode : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (initial : msg.benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.settledFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = ByteArray.empty ∧ ∀ root ∈ trace.settledFrames, root.sevm.caller ≠ a := by
  cases trace with
  | createCollision target collision result =>
    refine ⟨?_, fun root member => (List.not_mem_nil member).elim⟩
    rw [processMessageCall_createCollision_state_eq_noStateGas target collision result hsg]
    exact initial
  | createRun target collision evm core coreTrace result =>
    obtain ⟨post, callers⟩ := coreTrace.codeAt_callers_retained_noStateGas hsg caller
      (createAddress target) initial avoid
    refine ⟨?_, callers⟩
    rw [processMessageCall_createRun_state_eq_noStateGas target collision core result hsg]
    exact post
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    have disabled := processMessageCall.legacyAuthorization_disabled msg delegationDisabled
    have same : delegated = msg :=
      (Prod.mk.inj (Except.ok.inj (disabled.symm.trans delegation))).1.symm
    have executionCode : execMsg.benv.state.getCode a = ByteArray.empty := by
      rw [execMsgEq, same, messageCallExecutionMessage_getCode]
      exact initial
    have executionCaller : execMsg.caller ≠ a := by
      rw [execMsgEq, same, messageCallExecutionMessage_caller_eq]
      exact caller
    have executionGas : execMsg.benv.stat.rules.stateGas = none := by
      rw [execMsgEq, same, messageCallExecutionMessage_benv_stat]
      exact hsg
    have own : execMsg.currentTarget = a → execMsg.code = ByteArray.empty := by
      rw [execMsgEq, same]
      exact messageCallExecutionMessage_code_empty (callCode target).2 initial
    obtain ⟨post, callers⟩ := coreTrace.codeAt_callers_retained_noStateGas
      executionGas executionCaller own executionCode avoid
    refine ⟨?_, callers⟩
    rw [processMessageCall_callRun_state_eq_noStateGas target delegation execMsgEq core result hsg]
    exact post

/-- The original transaction supplies its checked sender and prepared code.
Refund credits, deletions and the selected touched-account sweep preserve
empty code at the endpoint. Failed transactions need no creation exclusion. -/
theorem TransactionTrace.codeAt_callers_retained_of_disabled
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {a : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (delegationDisabled : benv.stat.rules.delegationEnabled = false)
    (sender : trace.sender ≠ a)
    (initial : benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.settledFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = ByteArray.empty ∧ ∀ root ∈ trace.settledFrames, root.sevm.caller ≠ a := by
  have messageBenv := prepareMessage_benv trace.prepared
  have debitCode : trace.debitState.getCode a = benv.state.getCode a := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have messageCode : trace.msg.benv.state.getCode a = ByteArray.empty := by
    rw [messageBenv]
    exact debitCode.trans initial
  obtain ⟨post, callers⟩ := trace.message.codeAt_callers_retained_of_disabled
    (by rw [messageBenv]; exact hsg)
    (by rw [messageBenv]; exact delegationDisabled)
    (by rw [trace.msg_caller]; exact sender)
    (prepareMessage_fields trace.prepared).2 (prepareMessage_callCode trace.prepared)
    messageCode avoid
  refine ⟨?_, callers⟩
  obtain ⟨refundCounter, _, final⟩ := trace.exists_selectedFinalStateForm hsg
  rw [final]
  apply sweepTouchedAccounts_getCode_empty
  apply foldl_destroyAccount_getCode_empty
  rw [State.addBal_getCode, State.addBal_getCode]
  exact post

/-- The actual transaction fold propagates empty code and excludes callers
through retained frames, with no restriction on any discarded subtree. -/
theorem ApplyTransactionsTrace.codeAt_callers_retained_of_disabled
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput} {a : Adr}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (delegationDisabled : benv.stat.rules.delegationEnabled = false)
    (senders : trace.NoSenderAt a)
    (initial : benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.settledFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    finalBenv.state.getCode a = ByteArray.empty ∧
      ∀ root ∈ trace.settledFrames, root.sevm.caller ≠ a := by
  induction trace with
  | nil => exact ⟨initial, fun root member => (List.not_mem_nil member).elim⟩
  | cons head tail ih =>
    obtain ⟨middle, first⟩ := head.codeAt_callers_retained_of_disabled
      hsg delegationDisabled senders.1 initial
      (fun root member => avoid root (List.mem_append_left _ member))
    obtain ⟨last, later⟩ := ih hsg delegationDisabled senders.2 middle
      (fun root member => avoid root (List.mem_append_right _ member))
    refine ⟨last, ?_⟩
    intro root member
    rcases List.mem_append.mp member with before | after
    · exact first root before
    · exact later root after

end Blanc.ExecutionTrace
