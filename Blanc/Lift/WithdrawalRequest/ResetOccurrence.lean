import Blanc.Lift.WithdrawalRequest.BlockRequests

/-! Exact retained occurrence of the canonical protocol count reset. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.ExecutionTrace

private theorem systemProtocol_process_occurrence {benv : Benv}
    (fork : CoveredFork benv.stat.fork)
    (trace : ProcessMessageTrace (systemProtocolMsg benv) (.ok (systemProtocolPost benv))) :
    ∃ frame : Exec.Frame,
      trace.settledFrames = [frame] ∧
      frame.sevm = systemProtocolSevm benv ∧
      frame.pre = systemProtocolBase benv ∧
      frame.post = systemProtocolPost benv := by
  have entry : (Frame.ofCall (systemProtocolMsg benv)).enter =
      .run (initEvm (systemProtocolMsg benv)) := by
    exact Jaune.MessageExecution.frameEnter_eq_run_afterTransfer_of_notPrecompile
      (systemProtocolMsg benv) benv.beginTransaction withdrawalRequestPredeployAddress
      rfl rfl (withdrawalRequest_not_precompile fork)
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
    simp only [ProcessMessage, RunFrame, entry] at process
    rcases process with ⟨raw, impossible, _⟩
    cases impossible
  | @some pc sevm pre raw run =>
    have enter := (RunFrame.some_inv process).1
    have seedEq := FrameEntry.run.inj (enter.symm.trans entry)
    have pcEq := congrArg Evm.pc seedEq
    have sevmEq := congrArg Evm.sta seedEq
    have preEq := congrArg Evm.dyna seedEq
    change pc = 0 at pcEq
    change sevm = systemProtocolSevm benv at sevmEq
    change pre = systemProtocolBase benv at preEq
    subst pc sevm pre
    have rawEq : raw = .ok (systemProtocolPost benv) := by
      exact ((exec_iff_exec_eq _ _ _ _).mp ⟨run⟩).symm.trans (systemProtocol_exec fork)
    subst raw
    have clean : (systemProtocolPost benv).error = none := by
      rw [systemProtocolPost, systemFramePost_error]
      rfl
    have committed : Execution.commits (.ok (systemProtocolPost benv)) = true := by
      simp only [Execution.commits, clean, Option.isNone_none]
    have settled := ProcessMessage.settlementCommits_of_some_ok_clean process
      (by rw [clean]; rfl)
    refine ⟨Exec.Frame.ofRun run committed, ?_, rfl, rfl, rfl⟩
    rw [ProcessMessageTrace.settledFrames, ite_eq_left settled]
    rw [Exec.committedFrames, dite_eq_left committed,
      canonical_descendants run (systemProtocol_seed benv).2.2.2.1]

private theorem systemProtocol_call_occurrence {benv : Benv} {state : State} {out : MsgCallOutput}
    (fork : CoveredFork benv.stat.fork)
    (trace : MessageCallTrace (systemProtocolMsg benv) state out) :
    ∃ frame : Exec.Frame,
      trace.settledFrames = [frame] ∧
      frame.sevm = systemProtocolSevm benv ∧
      frame.pre = systemProtocolBase benv ∧
      frame.post = systemProtocolPost benv := by
  cases trace with
  | createCollision target collision result =>
    change false = true at target
    cases target
  | createRun target collision evm core coreTrace result =>
    change false = true at target
    cases target
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    change ∃ frame : Exec.Frame, coreTrace.settledFrames = [frame] ∧
      frame.sevm = systemProtocolSevm benv ∧ frame.pre = systemProtocolBase benv ∧
      frame.post = systemProtocolPost benv
    change Except.ok (systemProtocolMsg benv, 0) = Except.ok (delegated, refund) at delegation
    rcases Prod.mk.inj (Except.ok.inj delegation) with ⟨delegatedEq, refundEq⟩
    subst delegated refund
    have executionMessage : messageCallExecutionMessage (systemProtocolMsg benv) =
        systemProtocolMsg benv := by
      unfold messageCallExecutionMessage
      have nondelegated : getDelegatedCodeAddress (systemProtocolMsg benv).code = none :=
        withdrawalRequestCode_nondelegated
      rw [nondelegated]
    rw [executionMessage] at execMsgEq
    subst execMsg
    have evmEq : evm = systemProtocolPost benv :=
      Except.ok.inj (core.symm.trans (systemProtocol_message (benv := benv) fork))
    subst evm
    exact systemProtocol_process_occurrence fork coreTrace

/-- The retained canonical protocol withdrawal has one committed root and no
descendants. Its actual entry and post-machine agree with the constructed run. -/
theorem systemTrace_reset_occurrence {benv : Benv} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv withdrawalRequestPredeployAddress [] state out)
    (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    ∃ frame : Exec.Frame,
      trace.settledFrames = [frame] ∧
      frame.sevm = systemProtocolSevm benv ∧
      frame.pre = systemProtocolBase benv ∧
      frame.post = systemProtocolPost benv := by
  have messageEq : systemTransactionMessage benv withdrawalRequestPredeployAddress [] =
      systemProtocolMsg benv := by
    unfold systemTransactionMessage systemProtocolMsg
    rw [code]
  rcases trace with ⟨message, run⟩
  change ∃ frame : Exec.Frame, message.settledFrames = [frame] ∧
    frame.sevm = systemProtocolSevm benv ∧ frame.pre = systemProtocolBase benv ∧
    frame.post = systemProtocolPost benv
  generalize msgEq : systemTransactionMessage benv withdrawalRequestPredeployAddress [] = msg
    at message ⊢
  have canonical : msg = systemProtocolMsg benv := msgEq.symm.trans messageEq
  clear msgEq
  subst msg
  exact systemProtocol_call_occurrence fork message

/-- At every configured extension, the entire retained withdrawal subtree is
the actual nonstatic SYSTEM root. Its post-state is the withdrawal boundary,
its storage is the raw word update, and it contributes no submission payment.
The reset excess is at least two below the word maximum, independently of
fee correspondence or queue bounds. This is the withdrawal boundary, before
the remaining protocol processing. -/
theorem block_requests_reset_occurrence {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    ∃ frame : Exec.Frame,
      block.bodyTrace.requests.withdrawal.settledFrames = [frame] ∧
      frame.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
      frame.sevm.caller = systemAddress ∧
      frame.sevm.isStatic = false ∧
      frame.pre.state = block.bodyTrace.requestBenv.state ∧
      frame.post.state = block.bodyTrace.requests.withdrawalState ∧
      frame.post.getStor withdrawalRequestPredeployAddress =
        wordSystemStorage (block.bodyTrace.requestBenv.state.getStor
          withdrawalRequestPredeployAddress) ∧
      (frame.post.getStor withdrawalRequestPredeployAddress).get 1 = 0 ∧
      block.bodyTrace.requests.withdrawal.settledFrames.flatMap balanceFrameObservation = [frame] ∧
      block.bodyTrace.requests.withdrawal.settledFrames.flatMap submissionFramePayments = [] ∧
      ((frame.post.getStor withdrawalRequestPredeployAddress).get 0).toNat + 2 < 2 ^ 256 := by
  obtain ⟨frame, frames, sevm, entry, endpoint⟩ := systemTrace_reset_occurrence
    block.bodyTrace.requests.withdrawal (block.bodyTrace.requestBenv_covered block.covered)
    (block_request_code history block code)
  have seed := systemProtocol_seed block.bodyTrace.requestBenv
  have target : frame.sevm.currentTarget = withdrawalRequestPredeployAddress := by
    rw [sevm]
    exact seed.2.1
  have caller : frame.sevm.caller = systemAddress := by
    rw [sevm]
    exact seed.1
  have dynamic : frame.sevm.isStatic = false := by
    rw [sevm]
    exact seed.2.2.1
  have boundary : frame.post.state = block.bodyTrace.requests.withdrawalState := by
    rw [endpoint, (block_requests_result history block code).1]
    rfl
  have storage : frame.post.getStor withdrawalRequestPredeployAddress =
      wordSystemStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress) := by
    change frame.post.state.getStor withdrawalRequestPredeployAddress = _
    rw [boundary]
    exact block_requests_storage history block code
  refine ⟨frame, frames, target, caller, dynamic, ?_, boundary, storage, ?_, ?_, ?_, ?_⟩
  · rw [entry]
    rfl
  · change (frame.post.state.getStor withdrawalRequestPredeployAddress).get 1 = 0
    rw [boundary]
    exact block_requests_count_reset history block code
  · rw [frames]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact ite_eq_left ⟨target, dynamic⟩
  · rw [frames]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply ite_eq_right
    intro submission
    exact submission.2.1 caller
  · rw [storage]
    dsimp only [wordSystemStorage]
    rw [Stor.get_set_ne _ (by decide : (1 : B256) ≠ 0), Stor.get_set_self]
    let pointers := wordSystemPointers
      (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress)
    let total := pointers.get 1 + if pointers.get 0 = B256.max then 0 else pointers.get 0
    change (if (2 : B256) < total then total - 2 else 0).toNat + 2 < 2 ^ 256
    by_cases positive : (2 : B256) < total
    · rw [ite_eq_left positive, B256.toNat_sub_eq_of_le _ _ (B256.le_of_lt positive)]
      have positiveNat := B256.toNat_lt_toNat positive
      have totalBound := B256.toNat_lt total
      change 2 < total.toNat at positiveNat
      change total.toNat - 2 + 2 < 2 ^ 256
      omega
    · rw [ite_eq_right positive]
      change (0 : Nat) + 2 < 2 ^ 256
      decide

end Blanc.Lift.WithdrawalRequest
