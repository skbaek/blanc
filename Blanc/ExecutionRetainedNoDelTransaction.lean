import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionCommittedCell

/-!
Actual message and transaction deletion exclusion from conditional preservation
at complete-settlement-retained roots. Discarded cores have no raw-safety premise.
-/

namespace Blanc

open Jaune

/-- A committing outcome's actual post-machine NoDel is its outcome NoDel. -/
theorem Execution.noDel_of_committedPost {wa : Adr} {out : Execution}
    (committed : Execution.commits out = true)
    (preserved : Devm.NoDel wa (Execution.committedPost out committed)) :
    Execution.NoDel wa out := by
  cases out with
  | error error => cases committed
  | ok post => exact preserved

namespace ExecutionTrace

/-- A clean complete CALL settlement invokes only its own retained root law.
The existing message engine constructs the actual incoming NoDel. -/
theorem ProcessMessageTrace.noDel_of_settledRoots {wa : Adr}
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (clean : post.error.isNone = true)
    (initial : Msg.NoDel wa msg) (inherited : wa ∉ msg.inheritedDeletions)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) : Devm.NoDel wa post := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => exact ProcessMessage.inv_noDel (xl := .none) trivial process initial inherited
  | @some pc sevm pre raw run =>
    have settles : Frame.settlementCommits (Frame.ofCall msg) raw = true := by
      unfold Frame.settlementCommits
      rw [← (RunFrame.some_inv process).2]
      exact clean
    have committed := Frame.raw_commits_of_settlementCommits settles
    have member : Exec.Frame.ofRun run committed ∈
        (ProcessMessageTrace.mk _ (.some run) process).settledRoots := by
      simp only [ProcessMessageTrace.settledRoots, settles, ↓reduceIte,
        RetainedXlot.settledRoots, committed, ↓reduceDIte, List.mem_singleton]
    have callback : Xlot.InvNoDel wa (.some ⟨⟨pc, sevm, pre⟩, raw⟩) := by
      intro input
      exact Execution.noDel_of_committedPost committed
        (roots (Exec.Frame.ofRun run committed) member input)
    exact ProcessMessage.inv_noDel callback process initial inherited

/-- A clean COMPLETE CREATE settlement invokes the exact retained constructor
root. Code-deposit failure cannot satisfy the clean premise. -/
theorem ProcessCreateMessageTrace.noDel_of_settledRoots {wa : Adr}
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    (clean : post.error.isNone = true) (target : msg.currentTarget ≠ wa)
    (initial : Msg.NoDel wa msg) (inherited : wa ∉ msg.inheritedDeletions)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) : Devm.NoDel wa post := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => exact ProcessCreateMessage.inv_noDel (xl := .none) trivial process target initial inherited
  | @some pc sevm pre raw run =>
    have settles : Frame.settlementCommits (Frame.ofCreate msg) raw = true := by
      unfold Frame.settlementCommits
      rw [← (RunFrame.some_inv process).2]
      exact clean
    have committed := Frame.raw_commits_of_settlementCommits settles
    have member : Exec.Frame.ofRun run committed ∈
        (ProcessCreateMessageTrace.mk _ (.some run) process).settledRoots := by
      simp only [ProcessCreateMessageTrace.settledRoots, settles, ↓reduceIte,
        RetainedXlot.settledRoots, committed, ↓reduceDIte, List.mem_singleton]
    have callback : Xlot.InvNoDel wa (.some ⟨⟨pc, sevm, pre⟩, raw⟩) := by
      intro input
      exact Execution.noDel_of_committedPost committed
        (roots (Exec.Frame.ofRun run committed) member input)
    exact ProcessCreateMessage.inv_noDel callback process target initial inherited

/-- The actual message output excludes deletion from conditional laws on this
trace's complete-settlement roots. Failed core outputs discard their deletion
sets, including failed CREATE code deposit. -/
theorem MessageCallTrace.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (own : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (initial : Msg.NoDel wa msg) (inherited : wa ∉ msg.inheritedDeletions)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    wa ∉ out.accountsToDelete ∧ state.getCode wa = C := by
  refine ⟨?_, trace.code_eq hsg installed (installed ▸ initial.code) hCdel⟩
  cases trace with
  | createCollision target collision result =>
    have output := processMessageCall_createCollision_out_noStateGas hsg target
      collision result
    exact output.2 wa
  | createRun target collision evm core coreTrace result =>
    have targetNe : msg.currentTarget ≠ wa := ne_wa_of_not_hasCodeOrNonce initial.code
      (by simpa only [messageCreateCollision] using collision)
    exact (processMessageCall_createRun_noDel_of_clean hsg target collision core result
      (fun clean => (coreTrace.noDel_of_settledRoots clean targetNe initial inherited roots).atd)).2
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    obtain ⟨address, ownCode⟩ := own target
    obtain ⟨delegatedNoDel, -, delegatedInherited, -⟩ := messageCallDelegation_installed
      delegation initial (by rw [installed]; exact hCdel) inherited address ownCode
    have execNoDel : Msg.NoDel wa execMsg := by
      rw [execMsgEq]
      unfold messageCallExecutionMessage Msg.resolveCodeDelegation
      split <;> exact ⟨delegatedNoDel.ca, delegatedNoDel.code⟩
    have execInherited : wa ∉ execMsg.inheritedDeletions := by
      rw [execMsgEq]
      unfold messageCallExecutionMessage Msg.resolveCodeDelegation
      split <;> exact delegatedInherited
    exact (processMessageCall_callRun_noDel_of_clean hsg target delegation execMsgEq core result
      (fun clean => (coreTrace.noDel_of_settledRoots clean execNoDel execInherited roots).atd)).2

/-- Actual transaction deletion exclusion, message code and selected final
code from laws on this transaction's own complete-settlement roots. -/
theorem TransactionTrace.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    wa ∉ trace.messageOut.accountsToDelete ∧ trace.messageState.getCode wa = C ∧
      state.getCode wa = C := by
  have hbenv := prepareMessage_benv trace.prepared
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans installed
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have messageNoDel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hCne
  obtain ⟨notDeleted, messageCode⟩ := trace.message.noDel_of_settledRoots hCdel
    hmsgSg hmsgState (prepareMessage_own trace.prepared) messageNoDel
    (trace.not_mem_msg_inheritedDeletions wa) roots
  refine ⟨notDeleted, messageCode, ?_⟩
  exact (trace.cell_property_of_settledRoots 0 hsg installed hCne hCdel notDeleted
    (fun _ => True) (by intro R member ready; trivial) trivial).2

/-- The selected transaction list composes only its own settled-root laws,
retaining actual message-output exclusions and installed code at its endpoint. -/
theorem ApplyTransactionsTrace.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    trace.NoDelScheduled wa ∧ finalBenv.state.getCode wa = C := by
  induction trace with
  | nil => exact ⟨trivial, installed⟩
  | cons head tail ih =>
    have headRoots : ∀ R ∈ head.settledRoots,
        Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
      intro R member
      exact roots R (List.mem_append_left _ member)
    have tailRoots : ∀ R ∈ tail.settledRoots,
        Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
      intro R member
      exact roots R (List.mem_append_right _ member)
    obtain ⟨headNotDeleted, -, headCode⟩ :=
      head.noDel_of_settledRoots hCdel hCne hsg installed notCreated headRoots
    obtain ⟨tailNotDeleted, finalCode⟩ := ih hsg headCode notCreated tailRoots
    exact ⟨⟨headNotDeleted, tailNotDeleted⟩, finalCode⟩

end ExecutionTrace
end Blanc
