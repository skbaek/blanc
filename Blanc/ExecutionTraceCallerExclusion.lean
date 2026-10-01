import Blanc.ExecutionCallerExclusion
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionAccountingAdmission

/-! Transaction-only caller exclusion from the checked senders and actual raw CREATE roots. -/

namespace Blanc.ExecutionTrace

open Jaune

private theorem messageCallDelegation_code_own
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (address : msg.codeAddress = some msg.currentTarget)
    (code : msg.code = msg.benv.state.getCode msg.currentTarget) :
    delegated.code = delegated.benv.state.getCode delegated.currentTarget := by
  unfold messageCallDelegation at run
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

private theorem messageCallExecutionMessage_code_empty
    {msg : Msg} {a : Adr}
    (own : msg.code = msg.benv.state.getCode msg.currentTarget)
    (empty : msg.benv.state.getCode a = ByteArray.empty) :
    (messageCallExecutionMessage msg).currentTarget = a →
      (messageCallExecutionMessage msg).code = ByteArray.empty := by
  unfold messageCallExecutionMessage
  have none : getDelegatedCodeAddress ByteArray.empty = Option.none := by decide
  split
  · intro target
    rw [own, target, empty]
  · rename_i address delegated
    intro target
    have code : msg.code = ByteArray.empty := by rw [own, target, empty]
    rw [code, none] at delegated
    cases delegated

private theorem RetainedXlot.caller_excluded_of_runFrame
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (retained : RetainedXlot slot) (run : RunFrame frame slot out)
    (fork : CoveredFork frame.inner.benv.stat.fork)
    (caller : frame.inner.caller ≠ a)
    (code : frame.inner.codeAddress = Option.none ∨
      (frame.inner.currentTarget = a → frame.inner.benv.state.getCode a = ByteArray.empty →
        frame.inner.code = ByteArray.empty))
    (empty : ∀ root ∈ retained.rawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ retained.rawFrames,
      root.sevm.codeAddress = Option.none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ retained.rawFrames, root.sevm.caller ≠ a := by
  cases retained with
  | none => intro root member; simp only [RetainedXlot.rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution raw =>
    have enter := (RunFrame.some_inv run).1
    have rootFork : CoveredFork sevm.benvStat.fork := by
      rw [Frame.enter_run_benvStat enter]; exact fork
    have rootCaller : sevm.caller ≠ a := by
      rw [Frame.enter_run_caller enter]; exact caller
    have rootMember : (⟨pc, sevm, pre, execution, raw⟩ : Exec.Deriv) ∈
        (RetainedXlot.some raw).rawFrames := by
      simp only [RetainedXlot.rawFrames, Exec.rawFrameRoots]
      exact List.mem_cons_self
    have rootCode : sevm.currentTarget = a → sevm.code = ByteArray.empty := by
      intro target
      rcases code with create | own
      · exact False.elim (avoid _ rootMember
          ((Frame.enter_run_codeAddress enter).trans create) target)
      · rw [Frame.enter_run_code enter]
        exact own ((Frame.enter_run_currentTarget enter).symm.trans target)
          ((Frame.enter_run_getCode enter a).symm.trans (empty _ rootMember))
    exact fun root member =>
      (Exec.rawFrameRoots_caller_excluded raw rootFork rootCaller rootCode empty avoid
        root member).1

private theorem MessageCallTrace.caller_excluded
    {msg : Msg} {state : State} {out : MsgCallOutput} {a : Adr}
    (trace : MessageCallTrace msg state out)
    (fork : CoveredFork msg.benv.stat.fork) (caller : msg.caller ≠ a)
    (createAddress : msg.target.isNone = true → msg.codeAddress = none)
    (callCode : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (empty : ∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.rawFrames, root.sevm.caller ≠ a := by
  cases trace with
  | createCollision =>
    intro root member
    simp only [MessageCallTrace.rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
    exact RetainedXlot.caller_excluded_of_runFrame coreTrace.retained coreTrace.run
      (by change CoveredFork (processCreateMessage.msg msg).benv.stat.fork
          rw [processCreateMessage.msg_benvStat]; exact fork)
      caller (Or.inl (createAddress target)) empty avoid
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    subst execMsgEq
    have own := messageCallDelegation_code_own delegation
      (callCode target).1 (callCode target).2
    exact RetainedXlot.caller_excluded_of_runFrame coreTrace.retained coreTrace.run
      (by change CoveredFork (messageCallExecutionMessage delegated).benv.stat.fork
          rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]; exact fork)
      (by change (messageCallExecutionMessage delegated).caller ≠ a
          rw [messageCallExecutionMessage_caller_eq,
          messageCallDelegation_caller_eq delegation]; exact caller)
      (Or.inr (fun target empty => messageCallExecutionMessage_code_empty own
        (by rw [← messageCallExecutionMessage_getCode delegated a]; exact empty) target))
      empty avoid

/-- Every raw transaction caller is excluded from an address that stayed empty and was not created. -/
theorem TransactionTrace.caller_excluded
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {a : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) (sender : trace.sender ≠ a)
    (empty : ∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.rawFrames, root.sevm.caller ≠ a := by
  have callCode : trace.msg.target.isNone = false →
      trace.msg.codeAddress = some trace.msg.currentTarget ∧
        trace.msg.code = trace.msg.benv.state.getCode trace.msg.currentTarget := by
    have prepared := trace.prepared
    cases receiver : tx.type.receiver? with
    | none =>
      simp only [prepareMessage, receiver] at prepared
      rw [← Except.ok.inj prepared]
      intro target
      cases target
    | some target =>
      simp only [prepareMessage, receiver] at prepared
      rw [← Except.ok.inj prepared]
      intro _
      exact ⟨rfl, rfl⟩
  exact MessageCallTrace.caller_excluded trace.message
    (by rw [prepareMessage_benv trace.prepared]; exact fork)
    (by rw [trace.msg_caller]; exact sender)
    (prepareMessage_fields trace.prepared).2 callCode empty avoid

/-- Only the actual checked senders retained by this transaction traversal are excluded. -/
def ApplyTransactionsTrace.NoSenderAt (a : Adr) :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → Prop
  | .nil _ _ => True
  | .cons head tail => head.sender ≠ a ∧ tail.NoSenderAt a

private theorem ApplyTransactionsTrace.caller_excluded
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput} {a : Adr}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (fork : CoveredFork benv.stat.fork) (senders : trace.NoSenderAt a)
    (empty : ∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.rawFrames, root.sevm.caller ≠ a := by
  induction trace with
  | nil =>
    intro root member
    simp only [ApplyTransactionsTrace.rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
    have headCallers := head.caller_excluded fork senders.1
      (fun root member => empty root (List.mem_append_left _ member))
      (fun root member => avoid root (List.mem_append_left _ member))
    have tailCallers := ih fork senders.2
      (fun root member => empty root (List.mem_append_right _ member))
      (fun root member => avoid root (List.mem_append_right _ member))
    intro root member
    simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
    rcases member with member | member
    · exact headCallers root member
    · exact tailCallers root member

/-- Transaction senders are read from the checked transaction traces of each configured block. -/
def ConfiguredHistoryTrace.NoSenderAt (a : Adr) :
    ConfiguredHistoryTrace cfg checkpoint future → Prop
  | .refl _ _ _ => True
  | .step prior block => prior.NoSenderAt a ∧ block.bodyTrace.transactions.NoSenderAt a

private theorem ConfiguredHistoryTrace.txCallers_of_empty
    {cfg : ChainConfig} {checkpoint future : BlockChain} {a : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (senders : trace.NoSenderAt a)
    (empty : ∀ root ∈ trace.txRawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.txRawFrames, root.sevm.caller ≠ a := by
  induction trace with
  | refl =>
    intro root member
    simp only [ConfiguredHistoryTrace.txRawFrames, List.not_mem_nil] at member
  | step prior block ih =>
    have priorCallers := ih senders.1
      (fun root member => empty root (List.mem_append_left _ member))
      (fun root member => avoid root (List.mem_append_left _ member))
    have blockCallers := ApplyTransactionsTrace.caller_excluded block.bodyTrace.transactions
      block.covered senders.2
      (fun root member => empty root (List.mem_append_right _ member))
      (fun root member => avoid root (List.mem_append_right _ (by
        simp only [ConfiguredBlockTrace.rawFrames, AppliedBodyTrace.rawFrames, List.mem_append]
        exact Or.inl (Or.inr member))))
    intro root member
    simp only [ConfiguredHistoryTrace.txRawFrames, List.mem_append] at member
    rcases member with member | member
    · exact priorCallers root member
    · exact blockCallers root member

/-- Empty initial code, no recovered authority/sender, and no entered CREATE at `a`
exclude `a` as caller of every transaction raw frame. System frames are outside this conclusion. -/
theorem ConfiguredHistoryTrace.txRawFrames_caller_excluded
    {cfg : ChainConfig} {checkpoint future : BlockChain} {a : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (senders : trace.NoSenderAt a) (authorities : trace.NoAuthorityAt a)
    (avoid : ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (initial : checkpoint.state.getCode a = ByteArray.empty) :
    ∀ root ∈ trace.txRawFrames, root.sevm.caller ≠ a := by
  have empty := (trace.codeAt_empty authorities avoid initial).1
  exact ConfiguredHistoryTrace.txCallers_of_empty trace senders empty avoid

/-- Admission restricted to the transaction roots of a configured history. -/
def ConfiguredHistoryTrace.TxFrameAdmitted
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  ∀ root ∈ trace.txRawFrames, root.sevm.currentTarget = ca → entry root.sevm root.devm

/-- Derived transaction admission for consumers selecting any target address. -/
theorem ConfiguredHistoryTrace.txFrameAdmitted_caller_excluded
    {cfg : ChainConfig} {checkpoint future : BlockChain} {a ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (senders : trace.NoSenderAt a) (authorities : trace.NoAuthorityAt a)
    (avoid : ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (initial : checkpoint.state.getCode a = ByteArray.empty) :
    trace.TxFrameAdmitted ca (fun sevm _ => sevm.caller ≠ a) := by
  intro root member _
  exact trace.txRawFrames_caller_excluded senders authorities avoid initial root member

end Blanc.ExecutionTrace
