import Blanc.Weth10HolderFlowCompiled

/-!
Wrap-aware booked-storage accounting for local WETH10 action segments.

This module first proves the pointwise and aggregate storage equations from
the operational `Increase` / checked `Decrease` / `Transfer` witnesses in
`Weth10HolderFlowLocal`.  It then connects those equations to the retained
rollback-aware execution traversal.  No theorem below takes a balance or
supply endpoint equation as an input.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- Total word loss retained by one action's unique credit occurrence. -/
def FlowAction.bookedCreditLoss (action : FlowAction) : Nat :=
  match action.credit with
  | some credit => credit.loss
  | none => 0

/-- Mathematical supply entering during one contiguous local segment. -/
def LocalSegmentKind.bookedIn (kind : LocalSegmentKind)
    (action : FlowAction) : Nat :=
  match kind, action.atom with
  | .ordinaryMint, .ordinaryMint _ _ amount => amount
  | .flashCredit, .flashPair _ _ amount => amount
  | _, _ => 0

/-- Mathematical supply leaving during one contiguous local segment. -/
def LocalSegmentKind.bookedOut (kind : LocalSegmentKind)
    (action : FlowAction) : Nat :=
  match kind, action.atom with
  | .redemption, .redemption _ _ _ amount => amount
  | .flashRepayment, .flashPair _ _ amount => amount
  | _, _ => 0

/-- Aggregate modular loss of a segment's credit. -/
def LocalSegmentKind.bookedLoss (kind : LocalSegmentKind)
    (action : FlowAction) : Nat :=
  match kind with
  | .ordinaryMint | .ordinaryTransfer | .flashCredit =>
      action.bookedCreditLoss
  | .redemption | .flashRepayment => 0

/-- Every exact local segment satisfies the corresponding full booked-supply
equation.  Ordinary transfers have zero mathematical supply in/out; any
recipient wrap remains explicit on the right. -/
theorem LocalActionSegment.bookedSum_eq
    {kind : LocalSegmentKind} {action : FlowAction}
    {pre post : HolderBalances}
    (segment : LocalActionSegment kind action pre post) :
    sum pre + kind.bookedIn action =
      sum post + kind.bookedOut action + kind.bookedLoss action := by
  cases segment with
  | ordinaryMint rawRecipient recipient amountWord atom_eq credit_eq
      debit_eq increase =>
      unfold FlowAction.ExactCredit at credit_eq
      simpa [LocalSegmentKind.bookedIn, LocalSegmentKind.bookedOut,
        LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss,
        CreditOccurrence.loss, atom_eq, credit_eq] using
        (sum_increase_add_creditLoss increase)
  | ordinaryTransfer rawSource rawRecipient source recipient amountWord
      atom_eq transfer credit_eq debit_source =>
      unfold FlowAction.ExactCredit at credit_eq
      simpa [LocalSegmentKind.bookedIn, LocalSegmentKind.bookedOut,
        LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss,
        CreditOccurrence.loss, atom_eq, credit_eq] using
        (transfer_steps_sum_add_creditLoss transfer.amount_le
          transfer.decrease transfer.increase)
  | redemption rawSource source ethRecipient amountWord atom_eq credit_eq
      debit_source amount_le decrease =>
      simpa [LocalSegmentKind.bookedIn, LocalSegmentKind.bookedOut,
        LocalSegmentKind.bookedLoss, atom_eq] using
        (sum_decrease_add decrease amount_le).symm
  | flashCredit rawReceiver receiver amountWord atom_eq credit_eq
      debit_source increase =>
      unfold FlowAction.ExactCredit at credit_eq
      simpa [LocalSegmentKind.bookedIn, LocalSegmentKind.bookedOut,
        LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss,
        CreditOccurrence.loss, atom_eq, credit_eq] using
        (sum_increase_add_creditLoss increase)
  | flashRepayment rawReceiver receiver amountWord creditBefore atom_eq
      credit_eq debit_source amount_le decrease =>
      simpa [LocalSegmentKind.bookedIn, LocalSegmentKind.bookedOut,
        LocalSegmentKind.bookedLoss, atom_eq] using
        (sum_decrease_add decrease amount_le).symm

/-- Storage specialization of `LocalActionSegment.bookedSum_eq`. -/
theorem LocalActionSegment.balSum_eq
    {kind : LocalSegmentKind} {action : FlowAction} {pre post : Stor}
    (segment : LocalActionSegment kind action
      (Stor.rest pre) (Stor.rest post)) :
    balSum pre + kind.bookedIn action =
      balSum post + kind.bookedOut action + kind.bookedLoss action := by
  simpa only [balSum] using segment.bookedSum_eq

def localSegmentsBookedIn
    (segments : List (LocalSegmentKind × FlowAction)) : Nat :=
  (segments.map fun segment => segment.1.bookedIn segment.2).sum

def localSegmentsBookedOut
    (segments : List (LocalSegmentKind × FlowAction)) : Nat :=
  (segments.map fun segment => segment.1.bookedOut segment.2).sum

def localSegmentsBookedLoss
    (segments : List (LocalSegmentKind × FlowAction)) : Nat :=
  (segments.map fun segment => segment.1.bookedLoss segment.2).sum

/-- Exact aggregate booked-supply equation for a contiguous segment chain. -/
theorem LocalSegmentChain.bookedSum_eq
    {segments : List (LocalSegmentKind × FlowAction)}
    {pre post : HolderBalances}
    (chain : LocalSegmentChain segments pre post) :
    sum pre + localSegmentsBookedIn segments =
      sum post + localSegmentsBookedOut segments +
        localSegmentsBookedLoss segments := by
  induction chain with
  | nil balances =>
      simp [localSegmentsBookedIn, localSegmentsBookedOut,
        localSegmentsBookedLoss]
  | cons head rest ih =>
      have hhead := head.bookedSum_eq
      simp only [localSegmentsBookedIn, localSegmentsBookedOut,
        localSegmentsBookedLoss] at ih
      simp only [localSegmentsBookedIn, localSegmentsBookedOut,
        localSegmentsBookedLoss, List.map_cons, List.sum_cons]
      omega

/-- `balSum` form of the segment-chain theorem. -/
theorem LocalSegmentChain.balSum_eq
    {segments : List (LocalSegmentKind × FlowAction)} {pre post : Stor}
    (chain : LocalSegmentChain segments (Stor.rest pre) (Stor.rest post)) :
    balSum pre + localSegmentsBookedIn segments =
      balSum post + localSegmentsBookedOut segments +
        localSegmentsBookedLoss segments := by
  simpa only [balSum] using chain.bookedSum_eq

/-- Constructor-shaped aggregate equations for one action's own segments.
As with the holder equations, flash exposes the two sides of its callback gap
instead of equating the enclosing frame endpoints. -/
inductive LocalOwnBookedEquations (action : FlowAction)
    (pre post : HolderBalances) : Prop
  | ordinaryMint
      (equation : sum pre +
          LocalSegmentKind.ordinaryMint.bookedIn action =
        sum post + LocalSegmentKind.ordinaryMint.bookedOut action +
          LocalSegmentKind.ordinaryMint.bookedLoss action) :
      LocalOwnBookedEquations action pre post
  | ordinaryTransfer
      (equation : sum pre +
          LocalSegmentKind.ordinaryTransfer.bookedIn action =
        sum post + LocalSegmentKind.ordinaryTransfer.bookedOut action +
          LocalSegmentKind.ordinaryTransfer.bookedLoss action) :
      LocalOwnBookedEquations action pre post
  | redemption
      (equation : sum pre + LocalSegmentKind.redemption.bookedIn action =
        sum post + LocalSegmentKind.redemption.bookedOut action +
          LocalSegmentKind.redemption.bookedLoss action) :
      LocalOwnBookedEquations action pre post
  | flashPair (minted settle : HolderBalances)
      (mintEquation : sum pre +
          LocalSegmentKind.flashCredit.bookedIn action =
        sum minted + LocalSegmentKind.flashCredit.bookedOut action +
          LocalSegmentKind.flashCredit.bookedLoss action)
      (repaymentEquation : sum settle +
          LocalSegmentKind.flashRepayment.bookedIn action =
        sum post + LocalSegmentKind.flashRepayment.bookedOut action +
          LocalSegmentKind.flashRepayment.bookedLoss action) :
      LocalOwnBookedEquations action pre post

theorem LocalOwnEffect.booked_equations
    {action : FlowAction} {pre post : HolderBalances}
    (effect : LocalOwnEffect action pre post) :
    LocalOwnBookedEquations action pre post := by
  cases effect with
  | ordinaryMint segment =>
      exact .ordinaryMint segment.bookedSum_eq
  | ordinaryTransfer segment =>
      exact .ordinaryTransfer segment.bookedSum_eq
  | redemption segment =>
      exact .redemption segment.bookedSum_eq
  | flashPair mint repayment =>
      exact .flashPair _ _ mint.bookedSum_eq repayment.bookedSum_eq

/-! ## Rollback-aware retained-action extraction -/

/-- A noncommitting root contributes no committed frame. -/
theorem Exec.committedFrames_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (h : Execution.commits out ≠ true) :
    Blanc.Exec.committedFrames run = [] := by
  simp [Blanc.Exec.committedFrames, h]

theorem Exec.flowActions_eq_nil_of_error
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {err : EvmError × Devm}
    (run : Exec pc sevm pre (.error err)) :
    Blanc.Weth10.Exec.flowActions dp ca run = [] := by
  apply Exec.flowActions_eq_nil_of_not_commits run
  simp [Execution.commits]

/-- Membership in the executable action list retains the actual committed
frame and classifier equation that produced the action. -/
theorem Exec.mem_flowActions_iff
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (action : FlowAction) :
    action ∈ Blanc.Weth10.Exec.flowActions dp ca run ↔
      ∃ frame ∈ Blanc.Exec.committedFrames run,
        Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action := by
  simp [Blanc.Weth10.Exec.flowActions, List.mem_filterMap]

/-- Every retained action therefore has a concrete committing frame and an
exact WETH10 invocation witness, independently of any user-supplied log list. -/
theorem Exec.exists_exact_committedFrame_of_mem_flowActions
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {action : FlowAction}
    (h : action ∈ Blanc.Weth10.Exec.flowActions dp ca run) :
    ∃ frame ∈ Blanc.Exec.committedFrames run,
      Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
        Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame := by
  rcases (Exec.mem_flowActions_iff run action).mp h with
    ⟨frame, hframe, haction⟩
  exact ⟨frame, hframe, haction,
    Blanc.Weth10.Exec.Frame.exactInvocation_of_flowAction?_eq_some haction⟩

/-- With the raw root's installed-code and fresh-entry facts, retained-action
membership upgrades to the complete compiled-functional context. -/
theorem Exec.exists_authentic_committedFrame_of_mem_flowActions
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {action : FlowAction}
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty)
    (h : action ∈ Blanc.Weth10.Exec.flowActions dp ca run) :
    ∃ frame ∈ Blanc.Exec.committedFrames run,
      Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
        Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
  rcases (Exec.mem_flowActions_iff run action).mp h with
    ⟨frame, hframe, haction⟩
  exact ⟨frame, hframe, haction,
    Blanc.Weth10.Exec.Frame.authenticContext_of_mem_committedFrames
      run hcode hpc hmemory hframe haction⟩

/-- The executable action ledger is storage-authentic: every retained action
comes from an actual committed frame of the compiled WETH10 program, whose
functional effect supplies both the exact holder equations and the aggregate
booked-supply equation.  The flash case keeps its callback gap explicit in
`LocalOwnEffect` and in both equation families. -/
theorem Exec.exists_authenticLocalStorage_of_mem_flowActions
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {action : FlowAction}
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty)
    (h : action ∈ Blanc.Weth10.Exec.flowActions dp ca run) :
    ∃ frame ∈ Blanc.Exec.committedFrames run,
      Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
        Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame ∧
          ∃ ownPost : HolderBalances,
            LocalOwnEffect action
                (Stor.rest (Devm.getStor frame.pre ca)) ownPost ∧
              (∀ u : Adr, LocalOwnHolderEquations action
                (Stor.rest (Devm.getStor frame.pre ca)) ownPost u) ∧
              LocalOwnBookedEquations action
                (Stor.rest (Devm.getStor frame.pre ca)) ownPost := by
  rcases Exec.exists_authentic_committedFrame_of_mem_flowActions
    (run := run) hcode hpc hmemory h with
    ⟨frame, hframe, haction, context⟩
  rcases Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_flowAction?_eq_some context haction with
    ⟨ownPost, effect⟩
  exact ⟨frame, hframe, haction, context, ownPost, effect,
    fun u => effect.holder_equations u, effect.booked_equations⟩

theorem Exec.holderFlow_eq_zero_of_not_commits
    {dp : DeployParams} {ca u : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (h : Execution.commits out ≠ true) :
    holderFlowOfActions (Blanc.Weth10.Exec.flowActions dp ca run) u =
      HolderFlow.zero u := by
  rw [Exec.flowActions_eq_nil_of_not_commits run h]
  rfl

theorem Exec.holderCreditLoss_eq_zero_of_not_commits
    {dp : DeployParams} {ca u : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (h : Execution.commits out ≠ true) :
    holderCreditLossOfActions
      (Blanc.Weth10.Exec.flowActions dp ca run) u = 0 := by
  rw [Exec.flowActions_eq_nil_of_not_commits run h]
  rfl

/-! ## Origins throughout the retained history -/

/-- An action has an execution origin when it is computed from the
rollback-pruned committed-frame traversal of one actual `Exec` derivation. -/
def FlowAction.HasExecOrigin (dp : DeployParams) (ca : Adr)
    (action : FlowAction) : Prop :=
  ∃ (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution)
      (run : Exec pc sevm pre out) (frame : Exec.Frame),
    frame ∈ Blanc.Exec.committedFrames run ∧
      Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧ Blanc.Weth10.Exec.Frame.IsRoot frame

theorem FlowAction.HasExecOrigin.exists_exact_committedFrame
    {dp : DeployParams} {ca : Adr} {action : FlowAction}
    (origin : action.HasExecOrigin dp ca) :
    ∃ (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution)
        (run : Exec pc sevm pre out) (frame : Exec.Frame),
      frame ∈ Blanc.Exec.committedFrames run ∧
        Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
        Blanc.Weth10.Exec.Frame.IsRoot frame ∧ Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame := by
  rcases origin with
    ⟨pc, sevm, pre, out, run, frame, hframe, hclassified, hroot⟩
  exact ⟨pc, sevm, pre, out, run, frame,
    hframe, hclassified, hroot,
    Blanc.Weth10.Exec.Frame.exactInvocation_of_flowAction?_eq_some hclassified⟩

theorem RetainedXlot.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {xl : Xlot}
    (retained : RetainedXlot xl) (roots : retained.AllFramesRoot)
    {action : FlowAction}
    (h : action ∈ retained.flowActions dp ca) :
    action.HasExecOrigin dp ca := by
  cases retained with
  | none => simp [RetainedXlot.flowActions] at h
  | some run =>
      rcases (Exec.mem_flowActions_iff run action).mp h with
        ⟨frame, hframe, hclassified⟩
      exact ⟨_, _, _, _, run, frame, hframe, hclassified,
        roots frame hframe⟩

theorem ProcessMessageTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) {action : FlowAction}
    (h : action ∈ trace.retained.flowActions dp ca) :
    action.HasExecOrigin dp ca :=
  trace.retained.hasExecOrigin_of_mem_flowActions trace.allFramesRoot h

theorem ProcessCreateMessageTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) {action : FlowAction}
    (h : action ∈ trace.retained.flowActions dp ca) :
    action.HasExecOrigin dp ca :=
  trace.retained.hasExecOrigin_of_mem_flowActions trace.allFramesRoot h

private theorem frame_enter_run_memory_empty
    {frame : Frame} {child : Evm}
    (h : frame.enter = .run child) : child.dyna.memory = Mem.empty := by
  obtain ⟨benv, _, rfl⟩ := Frame.enter_run_inv h
  rfl

/-- At a raw call-message boundary, an installed WETH10 code witness in the
actual message state upgrades every retained action to an authentic compiled
frame. -/
theorem ProcessMessageTrace.exists_authenticFrame_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    (hcode : some (msg.benv.state.getCode ca).toList =
      Prog.compile (weth10 dp))
    {action : FlowAction}
    (h : action ∈ trace.retained.flowActions dp ca) :
    ∃ frame : Exec.Frame, Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
      Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => simp [RetainedXlot.flowActions] at h
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ := (RunFrame.some_inv hrun).1
      have hpreCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [Frame.enter_run_getCode henter ca]
        exact hcode
      rcases Exec.exists_authentic_committedFrame_of_mem_flowActions
        (run := run) hpreCode (Frame.enter_run_pc henter)
        (frame_enter_run_memory_empty henter) h with
        ⟨frame, _, haction, hcontext⟩
      exact ⟨frame, haction, hcontext⟩

theorem ProcessCreateMessageTrace.exists_authenticFrame_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (hcode : some (msg.benv.state.getCode ca).toList =
      Prog.compile (weth10 dp))
    {action : FlowAction}
    (h : action ∈ trace.retained.flowActions dp ca) :
    ∃ frame : Exec.Frame, Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
      Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => simp [RetainedXlot.flowActions] at h
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCreate msg).enter =
          .run ⟨pc, sevm, pre⟩ := (RunFrame.some_inv hrun).1
      have hpreCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [Frame.enter_run_getCode henter ca]
        simpa only [Frame.ofCreate, processCreateMessage.msg_getCode] using hcode
      rcases Exec.exists_authentic_committedFrame_of_mem_flowActions
        (run := run) hpreCode (Frame.enter_run_pc henter)
        (frame_enter_run_memory_empty henter) h with
        ⟨frame, _, haction, hcontext⟩
      exact ⟨frame, haction, hcontext⟩

theorem MessageCallTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out)
    {action : FlowAction} (h : action ∈ trace.flowActions dp ca) :
    action.HasExecOrigin dp ca := by
  cases trace with
  | createCollision htarget hcollision hresult =>
      simp [MessageCallTrace.flowActions] at h
  | createRun htarget hcollision evm hcore trace hresult =>
      simp only [MessageCallTrace.flowActions] at h
      split at h
      · simp at h
      · exact trace.hasExecOrigin_of_mem_flowActions h
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      exact trace.hasExecOrigin_of_mem_flowActions h

theorem TransactionTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {action : FlowAction} (h : action ∈ trace.flowActions dp ca) :
    action.HasExecOrigin dp ca :=
  trace.message.hasExecOrigin_of_mem_flowActions h

theorem ApplyTransactionsTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {action : FlowAction} (h : action ∈ trace.flowActions dp ca) :
    action.HasExecOrigin dp ca := by
  induction trace with
  | nil benv bout =>
      simp [ApplyTransactionsTrace.flowActions] at h
  | cons head tail ih =>
      simp only [ApplyTransactionsTrace.flowActions,
        List.mem_append] at h
      rcases h with hhead | htail
      · exact head.hasExecOrigin_of_mem_flowActions hhead
      · exact ih htail

theorem SystemMessageTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    {action : FlowAction} (h : action ∈ trace.flowActions dp ca) :
    action.HasExecOrigin dp ca :=
  trace.message.hasExecOrigin_of_mem_flowActions h

theorem RequestsTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    {action : FlowAction} (h : action ∈ trace.flowActions dp ca) :
    action.HasExecOrigin dp ca := by
  simp only [RequestsTrace.flowActions, List.mem_append] at h
  rcases h with hwithdrawal | hconsolidation
  · exact trace.withdrawal.hasExecOrigin_of_mem_flowActions hwithdrawal
  · exact trace.consolidation.hasExecOrigin_of_mem_flowActions hconsolidation

theorem AppliedBodyTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    {action : FlowAction} (h : action ∈ trace.flowActions dp ca) :
    action.HasExecOrigin dp ca := by
  simp only [AppliedBodyTrace.flowActions, List.mem_append] at h
  rcases h with ((hbeacon | hhistory) | htransactions) | hrequests
  · exact trace.beacon.hasExecOrigin_of_mem_flowActions hbeacon
  · exact trace.history.hasExecOrigin_of_mem_flowActions hhistory
  · exact trace.transactions.hasExecOrigin_of_mem_flowActions htransactions
  · exact trace.requests.hasExecOrigin_of_mem_flowActions hrequests

theorem AccountedBlock.hasExecOrigin_of_mem_actions
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock chainId dp ca pre post)
    {action : FlowAction} (h : action ∈ accounted.actions) :
    action.HasExecOrigin dp ca := by
  rw [accounted.actions_eq] at h
  exact accounted.bodyTrace.hasExecOrigin_of_mem_flowActions h

/-- Every action in the full Prague history has an actual retained `Exec`
origin and therefore inherits the rollback-pruned committed boundary. -/
theorem AccountedHistory.hasExecOrigin_of_mem_flowActions
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    {action : FlowAction} (h : action ∈ history.flowActions) :
    action.HasExecOrigin dp ca := by
  induction history with
  | refl hcfg hctx hid =>
      simp [AccountedHistory.flowActions] at h
  | step prior accounted ih =>
      simp only [AccountedHistory.flowActions, List.mem_append] at h
      rcases h with hprior | hblock
      · exact ih hprior
      · exact accounted.hasExecOrigin_of_mem_actions hblock

end Weth10

end Blanc
