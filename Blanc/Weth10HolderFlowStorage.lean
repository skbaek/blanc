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
      simpa only [LocalSegmentKind.bookedIn, atom_eq, LocalSegmentKind.bookedOut, add_zero,
        LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss, credit_eq,
        CreditOccurrence.loss] using (sum_increase_add_creditLoss increase)
  | ordinaryTransfer rawSource rawRecipient source recipient amountWord
      atom_eq transfer credit_eq debit_source =>
      unfold FlowAction.ExactCredit at credit_eq
      simpa only [LocalSegmentKind.bookedIn, add_zero, LocalSegmentKind.bookedOut,
        LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss, credit_eq,
        CreditOccurrence.loss] using
        (transfer_steps_sum_add_creditLoss transfer.amount_le transfer.decrease transfer.increase)
  | redemption rawSource source ethRecipient amountWord atom_eq credit_eq
      debit_source amount_le decrease =>
      simpa only [LocalSegmentKind.bookedIn, add_zero, LocalSegmentKind.bookedOut, atom_eq,
        LocalSegmentKind.bookedLoss] using (sum_decrease_add decrease amount_le).symm
  | flashCredit rawReceiver receiver amountWord atom_eq credit_eq
      debit_source increase =>
      unfold FlowAction.ExactCredit at credit_eq
      simpa only [LocalSegmentKind.bookedIn, atom_eq, LocalSegmentKind.bookedOut, add_zero,
        LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss, credit_eq,
        CreditOccurrence.loss] using (sum_increase_add_creditLoss increase)
  | flashRepayment rawReceiver receiver amountWord creditBefore atom_eq
      credit_eq debit_source amount_le decrease =>
      simpa only [LocalSegmentKind.bookedIn, add_zero, LocalSegmentKind.bookedOut, atom_eq,
        LocalSegmentKind.bookedLoss] using (sum_decrease_add decrease amount_le).symm

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
      simp only [localSegmentsBookedIn, List.map_nil, List.sum_nil, add_zero,
        localSegmentsBookedOut, localSegmentsBookedLoss]
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

/-- Membership in the executable action list retains the actual committed
frame and classifier equation that produced the action. -/
theorem Exec.mem_flowActions_iff
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (action : FlowAction) :
    action ∈ Blanc.Weth10.Exec.flowActions dp ca run ↔
      ∃ frame ∈ Blanc.Exec.committedFrames run,
        Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action := by
  simp only [flowActions, List.mem_filterMap]

/-- With the raw root's installed-code and fresh-entry facts, retained-action
membership upgrades to the complete compiled-functional context. -/
theorem Exec.exists_authentic_committedFrame_of_mem_flowActions
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {action : FlowAction}
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty)
    (h : action ∈ Blanc.Weth10.Exec.flowActions dp ca run)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∃ frame ∈ Blanc.Exec.committedFrames run,
      Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧
        Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
  rcases (Exec.mem_flowActions_iff run action).mp h with
    ⟨frame, hframe, haction⟩
  exact ⟨frame, hframe, haction,
    Blanc.Weth10.Exec.Frame.authenticContext_of_mem_committedFrames
      run hcode hpc hmemory hfork hframe haction⟩

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
    (h : action ∈ Blanc.Weth10.Exec.flowActions dp ca run)
    (hfork : CoveredFork sevm.benvStat.fork) :
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
    (run := run) hcode hpc hmemory h hfork with
    ⟨frame, hframe, haction, context⟩
  rcases Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_flowAction?_eq_some context haction with
    ⟨ownPost, effect⟩
  exact ⟨frame, hframe, haction, context, ownPost, effect,
    fun u => effect.holder_equations u, effect.booked_equations⟩

/-! ## Origins throughout the retained history -/

/-- An action has an execution origin when it is computed from the
rollback-pruned committed-frame traversal of one actual `Exec` derivation. -/
def FlowAction.HasExecOrigin (dp : DeployParams) (ca : Adr)
    (action : FlowAction) : Prop :=
  ∃ (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution)
      (run : Exec pc sevm pre out) (frame : Exec.Frame),
    frame ∈ Jaune.Exec.committedFrames run ∧
      Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action ∧ Blanc.Weth10.Exec.Frame.IsRoot frame

theorem RetainedXlot.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {xl : Xlot}
    (retained : RetainedXlot xl)
    (roots : Blanc.Weth10.RetainedXlot.AllFramesRoot retained)
    {action : FlowAction}
    (h : action ∈
      Blanc.Weth10.RetainedXlot.flowActions dp ca retained) :
    action.HasExecOrigin dp ca := by
  cases retained with
  | none => simp only [flowActions, List.not_mem_nil] at h
  | some run =>
      rcases (Exec.mem_flowActions_iff run action).mp h with
        ⟨frame, hframe, hclassified⟩
      exact ⟨_, _, _, _, run, frame, hframe, hclassified,
        roots frame hframe⟩

theorem ProcessMessageTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) {action : FlowAction}
    (h : action ∈ Blanc.Weth10.RetainedXlot.flowActions dp ca
      trace.retained) :
    action.HasExecOrigin dp ca :=
  RetainedXlot.hasExecOrigin_of_mem_flowActions trace.retained
    (ProcessMessageTrace.allFramesRoot trace) h

theorem ProcessCreateMessageTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) {action : FlowAction}
    (h : action ∈ Blanc.Weth10.RetainedXlot.flowActions dp ca
      trace.retained) :
    action.HasExecOrigin dp ca :=
  RetainedXlot.hasExecOrigin_of_mem_flowActions trace.retained
    (ProcessCreateMessageTrace.allFramesRoot trace) h

theorem MessageCallTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out)
    {action : FlowAction}
    (h : action ∈ Blanc.Weth10.MessageCallTrace.flowActions dp ca trace) :
    action.HasExecOrigin dp ca := by
  cases trace with
  | createCollision htarget hcollision hresult =>
      simp only [flowActions, List.not_mem_nil] at h
  | createRun htarget hcollision evm hcore trace hresult =>
      simp only [MessageCallTrace.flowActions] at h
      split at h
      · simp only [List.not_mem_nil] at h
      · exact
          ProcessCreateMessageTrace.hasExecOrigin_of_mem_flowActions trace h
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      exact ProcessMessageTrace.hasExecOrigin_of_mem_flowActions trace h

theorem TransactionTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {action : FlowAction}
    (h : action ∈ Blanc.Weth10.TransactionTrace.flowActions dp ca trace) :
    action.HasExecOrigin dp ca :=
  MessageCallTrace.hasExecOrigin_of_mem_flowActions trace.message h

theorem ApplyTransactionsTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {action : FlowAction}
    (h : action ∈
      Blanc.Weth10.ApplyTransactionsTrace.flowActions dp ca trace) :
    action.HasExecOrigin dp ca := by
  induction trace with
  | nil benv bout =>
      simp only [flowActions, List.not_mem_nil] at h
  | cons head tail ih =>
      simp only [ApplyTransactionsTrace.flowActions,
        List.mem_append] at h
      rcases h with hhead | htail
      · exact TransactionTrace.hasExecOrigin_of_mem_flowActions head hhead
      · exact ih htail

theorem SystemMessageTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    {action : FlowAction}
    (h : action ∈ Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace) :
    action.HasExecOrigin dp ca :=
  MessageCallTrace.hasExecOrigin_of_mem_flowActions trace.message h

theorem RequestsTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    {action : FlowAction}
    (h : action ∈ Blanc.Weth10.RequestsTrace.flowActions dp ca trace) :
    action.HasExecOrigin dp ca := by
  simp only [RequestsTrace.flowActions, List.mem_append] at h
  rcases h with hwithdrawal | hconsolidation
  · exact SystemMessageTrace.hasExecOrigin_of_mem_flowActions
      trace.withdrawal hwithdrawal
  · exact SystemMessageTrace.hasExecOrigin_of_mem_flowActions
      trace.consolidation hconsolidation

theorem AppliedBodyTrace.hasExecOrigin_of_mem_flowActions
    {dp : DeployParams} {ca : Adr} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    {action : FlowAction}
    (h : action ∈ Blanc.Weth10.AppliedBodyTrace.flowActions dp ca trace) :
    action.HasExecOrigin dp ca := by
  simp only [AppliedBodyTrace.flowActions, List.mem_append] at h
  rcases h with ((hbeacon | hhistory) | htransactions) | hrequests
  · exact SystemMessageTrace.hasExecOrigin_of_mem_flowActions
      trace.beacon hbeacon
  · exact SystemMessageTrace.hasExecOrigin_of_mem_flowActions
      trace.history hhistory
  · exact ApplyTransactionsTrace.hasExecOrigin_of_mem_flowActions
      trace.transactions htransactions
  · exact RequestsTrace.hasExecOrigin_of_mem_flowActions
      trace.requests hrequests

end Weth10

end Blanc
