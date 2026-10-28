import Blanc.ExecutionNonceCode
import Blanc.Lift.CallerProvenance
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceSettledOrigin

/-! Nonempty code observed during retained execution, through message and
transaction settlement. Final account-deletion exclusion is explicit. -/

namespace Blanc

open Jaune

/-- Clean CALL settlement preserves the raw committed deletion set. -/
theorem ProcessMessage.ok_atd_eq_committedPost
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (process : ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (committed : Execution.commits out = true) :
    post.accountsToDelete = (Execution.committedPost out committed).accountsToDelete := by
  have settled := (RunFrame.some_inv process).2
  cases out with
  | error error => cases committed
  | ok raw =>
    cases clean : raw.error with
    | none =>
      simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
        processMessage.settle, executeCode.handleErrorWith_ok, Except.bind_ok, clean,
        Option.isSome_none, Except.ok.injEq] at settled
      have atd := congrArg Devm.accountsToDelete settled
      exact atd
    | some error =>
      simp only [Execution.commits, clean, Option.isNone_some, Bool.false_eq_true] at committed

end Blanc

namespace Blanc.ExecutionTrace

open Jaune

/-- Complete CALL settlement keeps the raw code of its actual retained root. -/
theorem ProcessMessageTrace.settledRoot_post_code
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) (a : Adr) :
    post.getCode a = R.post.getCode a := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => cases member
  | some run =>
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      next committed =>
        rw [List.mem_singleton] at member
        subst R
        exact congrArg (fun state : State => state.getCode a)
          (ProcessMessage.ok_state_eq_committedPost process committed)
      · cases member
    · cases member

/-- Successful CREATE deposit preserves every nonempty code in its retained
raw root. The collision guard and constructor nonce exclude its own target. -/
theorem ProcessCreateMessageTrace.settledRoot_post_code_of_nonempty
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none)
    (unprotected : ¬ State.Protected msg.benv.state msg.currentTarget)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) {a : Adr}
    (nonempty : (R.post.getCode a).toList ≠ []) :
    post.getCode a = R.post.getCode a := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => cases member
  | some run =>
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    next settles =>
      simp only [RetainedXlot.settledRoots] at member
      split at member
      next committed =>
        rw [List.mem_singleton] at member
        subst R
        obtain ⟨enter, settled⟩ := RunFrame.some_inv process
        have childGas : _ := Frame.enter_run_benvStat enter
        have gas : _ := processCreateMessage.msg_benvStat msg
        have rawEmpty := Exec.create_raw_target_code_empty_noStateGas enter run committed
          (by rw [childGas]; change (processCreateMessage.msg msg).benv.stat.rules.stateGas = none
              rw [gas]; exact hsg)
          (not_ne_iff.mp (fun h => unprotected (Or.inl h)))
          (not_ne_iff.mp (fun h => unprotected (Or.inr h)))
        have different : msg.currentTarget ≠ a := by
          intro same
          apply nonempty
          change ((Execution.committedPost _ committed).getCode a).toList = []
          rw [← same, rawEmpty]
          exact ByteArray.toList_empty
        have clean : post.error.isSome = false := by
          have cleanNone : post.error.isNone = true := by
            simpa only [Frame.settlementCommits, ← settled] using settles
          cases eq : post.error with
          | none => rfl
          | some error => rw [eq] at cleanNone; cases cleanNone
        obtain ⟨inner, innerRun, _, code, stateEq⟩ :=
          ProcessCreateMessage.ok_setCode_state_of_clean process clean
        have rawEq := ProcessMessage.ok_state_eq_committedPost innerRun committed
        change post.state.getCode a = _
        rw [stateEq, rawEq]
        exact State.setCode_get_code_ne different
      · cases member
    · cases member

/-- The settled message wrapper preserves nonempty code at its retained raw
endpoint, including top-level creation and delegated CALL preparation. -/
theorem MessageCallTrace.settledRoot_post_code_of_nonempty
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) {a : Adr}
    (nonempty : (R.post.getCode a).toList ≠ []) :
    state.getCode a = R.post.getCode a := by
  cases trace with
  | createCollision => cases member
  | createRun target collision evm core inner result =>
    rw [processMessageCall_createRun_state_eq_noStateGas target collision core result hsg]
    exact inner.settledRoot_post_code_of_nonempty hsg
      (messageCreateCollision_false_target_unprotected collision) member nonempty
  | callRun target delegated refund delegation execMsg execMsgEq evm core inner result =>
    rw [processMessageCall_callRun_state_eq_noStateGas target delegation execMsgEq core result hsg]
    exact inner.settledRoot_post_code member a

/-- An observation at an original retained node reaches the settled message
state. The account need not exist at message entry. -/
theorem MessageCallTrace.retainedNode_getCode_noStateGas
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) {a : Adr}
    (nonempty : (N.devm.getCode a).toList ≠ []) :
    state.getCode a = N.devm.getCode a := by
  have inFrames : R ∈ trace.settledFrames := by
    rw [trace.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, member, by
      simp only [Exec.committedFrames, R.committed, ↓reduceDIte]
      exact List.mem_cons_self⟩
  have raw := trace.mem_rawFrames_of_mem_settledFrames R inFrames
  have rootGas : R.sevm.benvStat.rules.stateGas = none :=
    (trace.rootEntryIn (F := fun fork => fork.ruleSet.stateGas = none) hsg _ raw).2
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp retained
  have same := (Exec.retainedNodes_code_after_split_noStateGas R.run R.committed
    rootGas split nonempty).1
  exact (trace.settledRoot_post_code_of_nonempty hsg member
    (by change ((Execution.committedPost R.out R.committed).getCode a).toList ≠ []
        rw [same]; exact nonempty)).trans same

/-- CALL core deletion facts come from the actual retained root, independently
of code installation or the account's creation time. -/
theorem ProcessMessageTrace.settledRoot_post_atd
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) :
    post.accountsToDelete = R.post.accountsToDelete := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => cases member
  | some run =>
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      next committed =>
        rw [List.mem_singleton] at member
        subst R
        exact ProcessMessage.ok_atd_eq_committedPost process committed
      · cases member
    · cases member

/-- Successful code deposit preserves the retained constructor's deletion set.
Failed code deposit contributes no retained root. -/
theorem ProcessCreateMessageTrace.settledRoot_post_atd
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) :
    post.accountsToDelete = R.post.accountsToDelete := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => cases member
  | some run =>
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    next settles =>
      simp only [RetainedXlot.settledRoots] at member
      split at member
      next committed =>
        rw [List.mem_singleton] at member
        subst R
        have clean : post.error.isSome = false := by
          have cleanNone : post.error.isNone = true := by
            simpa only [Frame.settlementCommits, ← (RunFrame.some_inv process).2] using settles
          cases eq : post.error with
          | none => rfl
          | some error => rw [eq] at cleanNone; cases cleanNone
        obtain ⟨inner, charged, innerRun, _, charge, installed⟩ :=
          ProcessCreateMessage.ok_charge_of_clean process clean
        rw [installed]
        change charged.accountsToDelete = _
        have atd : charged.accountsToDelete = inner.accountsToDelete :=
          congrArg Prod.fst (chargeCodeGas_delSets_ok charge)
        exact atd.trans (ProcessMessage.ok_atd_eq_committedPost innerRun committed)
      · cases member
    · cases member

/-- A selected retained root's deletion exclusion reaches the actual message
output. No nonempty-code or not-created-at-entry hypothesis is needed. -/
theorem MessageCallTrace.not_mem_accountsToDelete_of_settledRoot
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) {a : Adr}
    (notDeleted : a ∉ R.post.accountsToDelete) : a ∉ out.accountsToDelete := by
  cases trace with
  | createCollision => cases member
  | createRun target collision evm core inner result =>
    exact (processMessageCall_createRun_noDel_of_clean hsg target collision core result
      (fun _ => inner.settledRoot_post_atd member ▸ notDeleted)).2
  | callRun target delegated refund delegation execMsg execMsgEq evm core inner result =>
    exact (processMessageCall_callRun_noDel_of_clean hsg target delegation execMsgEq core result
      (fun _ => inner.settledRoot_post_atd member ▸ notDeleted)).2

/-- Deletion exclusion from the selected retained root supplies the exact
transaction output premise required for final code transport. -/
theorem TransactionTrace.not_mem_accountsToDelete_of_settledRoot
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) {a : Adr}
    (notDeleted : a ∉ R.post.accountsToDelete) : a ∉ trace.messageOut.accountsToDelete := by
  exact trace.message.not_mem_accountsToDelete_of_settledRoot
    (by rw [prepareMessage_benv trace.prepared]; exact hsg) member notDeleted

/-- The exact final deletion set is the only additional code obligation after
the settled message: refunds and fees change balances, and empty-account sweep
cannot erase the observed nonempty code. -/
theorem TransactionTrace.retainedNode_getCode_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) {a : Adr}
    (nonempty : (N.devm.getCode a).toList ≠ [])
    (notDeleted : a ∉ trace.messageOut.accountsToDelete) :
    state.getCode a = N.devm.getCode a := by
  have messageCode := trace.message.retainedNode_getCode_noStateGas
    (by rw [prepareMessage_benv trace.prepared]; exact hsg) member retained nonempty
  obtain ⟨refund, _, final⟩ := trace.exists_selectedFinalStateForm hsg
  have notList : ∀ x ∈ trace.messageOut.accountsToDelete.toList, x ≠ a :=
    fun x hx equal => notDeleted (equal ▸ Std.HashSet.mem_toList.mp hx)
  rw [final, sweepTouchedAccounts_getCode_of_nonempty,
    foldl_destroyAccount_getCode_ne _ notList, State.addBal_getCode, State.addBal_getCode,
    messageCode]
  rw [foldl_destroyAccount_getCode_ne _ notList, State.addBal_getCode, State.addBal_getCode,
    messageCode]
  exact nonempty

end Blanc.ExecutionTrace
