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

end Blanc.ExecutionTrace
