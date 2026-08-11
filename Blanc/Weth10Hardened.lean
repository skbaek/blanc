import Blanc.Weth10AllowanceDispatch

/-!
Hardened permanent outflow for the exact Blanc WETH10 runtime.

Two results about `hardenedOutflow`, the sub-sum of a holder's permanent
outflow whose debits carry an attribution witness.

The first is unconditional: the hardened sub-sum never exceeds the holder's
permanent outflow, which is the public `redeemed + externalTransferredOut`
total of the holder-flow fold.  Reaching that public total is itself work,
because the two structures are parallel recursions over the same trace with
different carriers — the chronological `CountedFrame` ledger and the
`FlowObservation` list — and a flash invocation's counted record follows its
callback subtree while its action precedes it.  `LedgerMirrors` carries the
reconciliation through the whole retained trace tower, claiming only that the
sums agree, which the flash swap leaves untouched.

The second is the collision-free equality: with the trace-local
`NoAllowanceKeyCollision` hypothesis, every counted debit of the holder's
balance is hardened, so the two totals coincide.  The hypothesis is consumed
at exactly one point, `CountedFrame.hardenedContribution_eq_permanentOutflow`,
where the projected key an allowance-branch debit read is matched against the
projected key the governing store wrote: equal keys force equal raw pairs, so
an `approve` root's clean `CALLER` owner word and a `permit` root's recovered
owner word both normalize to the debited holder.  Direct debits, the raw-word
self-bypass and flash settlement reach the same conclusion without it.

Everything here is computed from retained execution evidence.  No definition
or theorem below assumes a conservation equation, a global allowance-key
injectivity, or — as the equality's unused `_hstable` binder records — a
stable checkpoint.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Permanent-outflow sums -/

/-- One classified atom's permanent outflow for holder `u`: committed ETH
redemption plus committed external token transfer out. -/
def FlowAtom.outflow (atom : FlowAtom) (u : Adr) : Nat :=
  (atom.holderFlow u).redeemed + (atom.holderFlow u).externalTransferredOut

theorem CountedFrame.permanentOutflow_eq (record : CountedFrame) (u : Adr) :
    record.permanentOutflow u =
      match record.action with
      | some action => action.atom.outflow u
      | none => 0 := rfl

@[simp] theorem FlowAtom.outflow_ordinaryMint (raw : B256) (recipient : Adr)
    (amount : Nat) (u : Adr) :
    (FlowAtom.ordinaryMint raw recipient amount).outflow u = 0 := by
  by_cases hrec : recipient = u <;>
    simp [FlowAtom.outflow, FlowAtom.holderFlow, HolderFlow.zero, hrec]

@[simp] theorem FlowAtom.outflow_flashPair (raw : B256) (receiver : Adr)
    (amount : Nat) (u : Adr) :
    (FlowAtom.flashPair raw receiver amount).outflow u = 0 := by
  by_cases hrec : receiver = u <;>
    simp [FlowAtom.outflow, FlowAtom.holderFlow, HolderFlow.zero, hrec]

/-- A redemption carries permanent outflow for `u` only when `u` is its
normalized source. -/
theorem FlowAtom.source_of_outflow_redemption {raw : B256}
    {source ethRecipient : Adr} {amount : Nat} {u : Adr}
    (h : (FlowAtom.redemption raw source ethRecipient amount).outflow u ≠ 0) :
    source = u := by
  by_cases hsource : source = u
  · exact hsource
  · simp [FlowAtom.outflow, FlowAtom.holderFlow, HolderFlow.zero, hsource] at h

/-- A transfer carries permanent outflow for `u` only when `u` is its
normalized source. -/
theorem FlowAtom.source_of_outflow_transfer {rawSource rawRecipient : B256}
    {source recipient : Adr} {amount : Nat} {u : Adr}
    (h : (FlowAtom.transfer rawSource rawRecipient source recipient
      amount).outflow u ≠ 0) :
    source = u := by
  by_cases hsource : source = u
  · exact hsource
  · by_cases hrecipient : recipient = u <;>
      simp [FlowAtom.outflow, FlowAtom.holderFlow, HolderFlow.zero, hsource,
        hrecipient] at h

/-- Total permanent outflow of holder `u` recorded by a counted ledger. -/
def ledgerOutflow (u : Adr) : List CountedFrame → Nat
  | [] => 0
  | frame :: rest => frame.permanentOutflow u + ledgerOutflow u rest

/-- Total permanent outflow of holder `u` recorded by a flow-action list. -/
def actionOutflow (u : Adr) : List FlowAction → Nat
  | [] => 0
  | action :: rest =>
      ((action.atom.holderFlow u).redeemed +
          (action.atom.holderFlow u).externalTransferredOut) +
        actionOutflow u rest

@[simp] theorem ledgerOutflow_nil (u : Adr) : ledgerOutflow u [] = 0 := rfl

@[simp] theorem actionOutflow_nil (u : Adr) : actionOutflow u [] = 0 := rfl

theorem ledgerOutflow_append (u : Adr) (left right : List CountedFrame) :
    ledgerOutflow u (left ++ right) =
      ledgerOutflow u left + ledgerOutflow u right := by
  induction left with
  | nil => simp [ledgerOutflow]
  | cons frame rest ih => simp [ledgerOutflow, ih, Nat.add_assoc]

theorem actionOutflow_append (u : Adr) (left right : List FlowAction) :
    actionOutflow u (left ++ right) =
      actionOutflow u left + actionOutflow u right := by
  induction left with
  | nil => simp [actionOutflow]
  | cons action rest ih => simp [actionOutflow, ih, Nat.add_assoc]

/-! ## Selector separations

The classified atom, the debit provenance and the allowance visit of one
invocation are computed by three if-chains that test the dispatched selector
in different orders.  Reconciling them needs exactly the separations below;
every other branch of every chain is decided by a test the atom chain has
already passed. -/

theorem transferFromSelector_ne_transferSelector :
    transferFromSelector ≠ transferSelector := by decide +kernel

theorem transferFromSelector_ne_transferAndCallSelector :
    transferFromSelector ≠ transferAndCallSelector := by decide +kernel

theorem transferFromSelector_ne_withdrawSelector :
    transferFromSelector ≠ withdrawSelector := by decide +kernel

theorem transferFromSelector_ne_withdrawToSelector :
    transferFromSelector ≠ withdrawToSelector := by decide +kernel

theorem transferFromSelector_ne_approveSelector :
    transferFromSelector ≠ approveSelector := by decide +kernel

theorem transferFromSelector_ne_approveAndCallSelector :
    transferFromSelector ≠ approveAndCallSelector := by decide +kernel

theorem transferFromSelector_ne_permitSelector :
    transferFromSelector ≠ permitSelector := by decide +kernel

theorem withdrawFromSelector_ne_transferSelector :
    withdrawFromSelector ≠ transferSelector := by decide +kernel

theorem withdrawFromSelector_ne_transferAndCallSelector :
    withdrawFromSelector ≠ transferAndCallSelector := by decide +kernel

theorem withdrawFromSelector_ne_withdrawSelector :
    withdrawFromSelector ≠ withdrawSelector := by decide +kernel

theorem withdrawFromSelector_ne_withdrawToSelector :
    withdrawFromSelector ≠ withdrawToSelector := by decide +kernel

theorem withdrawFromSelector_ne_transferFromSelector :
    withdrawFromSelector ≠ transferFromSelector := by decide +kernel

theorem withdrawFromSelector_ne_approveSelector :
    withdrawFromSelector ≠ approveSelector := by decide +kernel

theorem withdrawFromSelector_ne_approveAndCallSelector :
    withdrawFromSelector ≠ approveAndCallSelector := by decide +kernel

theorem withdrawFromSelector_ne_permitSelector :
    withdrawFromSelector ≠ permitSelector := by decide +kernel

/-! ## The ledger/action mirror -/

/-- One counted record is retained when some committed frame produced it.
The attribution ledger stores only the record, so every fact relating a
record's allowance visit to its classified action must travel with this
witness. -/
def CountedFrame.HasFrameOrigin (dp : DeployParams) (ca : Adr)
    (record : CountedFrame) : Prop :=
  ∃ frame : Exec.Frame, record = CountedFrame.ofFrame dp ca frame

/-- A counted ledger mirrors an action list: every record is retained, and the
two carry the same permanent outflow for every holder.  The two structures are
built by parallel recursions that differ in the placement of a flash
invocation's own record, so only the sums are claimed equal. -/
structure LedgerMirrors (dp : DeployParams) (ca : Adr)
    (ledger : List CountedFrame) (actions : List FlowAction) : Prop where
  origins : ∀ record ∈ ledger, record.HasFrameOrigin dp ca
  outflow : ∀ u : Adr, ledgerOutflow u ledger = actionOutflow u actions

theorem LedgerMirrors.nil (dp : DeployParams) (ca : Adr) :
    LedgerMirrors dp ca [] [] :=
  ⟨by simp, by simp⟩

theorem LedgerMirrors.append {dp : DeployParams} {ca : Adr}
    {leftLedger rightLedger : List CountedFrame}
    {leftActions rightActions : List FlowAction}
    (left : LedgerMirrors dp ca leftLedger leftActions)
    (right : LedgerMirrors dp ca rightLedger rightActions) :
    LedgerMirrors dp ca (leftLedger ++ rightLedger)
      (leftActions ++ rightActions) := by
  refine ⟨fun record hrecord => ?_, fun u => ?_⟩
  · rcases List.mem_append.mp hrecord with h | h
    · exact left.origins record h
    · exact right.origins record h
  · rw [ledgerOutflow_append, actionOutflow_append, left.outflow u,
      right.outflow u]

/-- The flash placement swap: the counted record follows its subtree while the
action precedes it, and the sums are unaffected. -/
theorem LedgerMirrors.append_comm {dp : DeployParams} {ca : Adr}
    {leftLedger rightLedger : List CountedFrame}
    {leftActions rightActions : List FlowAction}
    (left : LedgerMirrors dp ca leftLedger leftActions)
    (right : LedgerMirrors dp ca rightLedger rightActions) :
    LedgerMirrors dp ca (leftLedger ++ rightLedger)
      (rightActions ++ leftActions) := by
  refine ⟨(left.append right).origins, fun u => ?_⟩
  rw [ledgerOutflow_append, actionOutflow_append, left.outflow u,
    right.outflow u, Nat.add_comm]

/-- One committed frame's own record mirrors its classified action. -/
theorem LedgerMirrors.ofFrame (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) :
    LedgerMirrors dp ca [CountedFrame.ofFrame dp ca frame]
      ((frame.flowAction? dp ca).toList) := by
  refine ⟨fun record hrecord => ?_, fun u => ?_⟩
  · rw [List.mem_singleton.mp hrecord]
    exact ⟨frame, rfl⟩
  · cases haction : frame.flowAction? dp ca with
    | none =>
        simp [ledgerOutflow, CountedFrame.permanentOutflow,
          CountedFrame.ofFrame, haction]
    | some action =>
        simp [ledgerOutflow, actionOutflow, CountedFrame.permanentOutflow,
          CountedFrame.ofFrame, haction]

/-- One committed frame's own record placed around its descendant stream
mirrors that frame's action prefixed to the descendant actions. -/
theorem LedgerMirrors.frameContribution {dp : DeployParams} {ca : Adr}
    (frame : Exec.Frame) {inner : List CountedFrame}
    {innerActions : List FlowAction}
    (h : LedgerMirrors dp ca inner innerActions) :
    LedgerMirrors dp ca (Exec.frameContribution dp ca frame inner)
      ((frame.flowAction? dp ca).toList ++ innerActions) := by
  by_cases hexact : frame.exactInvocation dp ca
  · by_cases hflash : isFlashInvocation frame.sevm = true
    · rw [Exec.frameContribution_eq_append dp ca frame inner hexact hflash]
      exact h.append_comm (LedgerMirrors.ofFrame dp ca frame)
    · rw [Exec.frameContribution_eq_cons dp ca frame inner hexact
        (by simpa using hflash)]
      exact (LedgerMirrors.ofFrame dp ca frame).append h
  · rw [Exec.frameContribution_eq_inner dp ca frame inner hexact]
    have hnone : frame.flowAction? dp ca = none := by
      cases haction : frame.flowAction? dp ca with
      | none => rfl
      | some action =>
          exact absurd (frame.exactInvocation_of_flowAction?_eq_some haction)
            hexact
    simpa [hnone] using h

/-- The counted stream of a derivation's committed descendants mirrors their
classified actions. -/
theorem Exec.ledgerMirrors_attributionInner (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    LedgerMirrors dp ca (Exec.attributionInner dp ca run)
      (Exec.descendantActions dp ca run) := by
  induction run with
  | halt hstep =>
      simpa only [Exec.attributionInner, Exec.descendantActions,
        Exec.descendantFrames, List.filterMap_nil] using LedgerMirrors.nil dp ca
  | cont hstep next ih =>
      simpa only [Exec.attributionInner, Exec.descendantActions,
        Exec.descendantFrames] using ih
  | doneErr hstep henter hresume =>
      simpa only [Exec.attributionInner, Exec.descendantActions,
        Exec.descendantFrames, List.filterMap_nil] using LedgerMirrors.nil dp ca
  | doneOk hstep henter hresume next ih =>
      simpa only [Exec.attributionInner, Exec.descendantActions,
        Exec.descendantFrames] using ih
  | runErr hstep henter child hresume ihChild =>
      simpa only [Exec.attributionInner, Exec.descendantActions,
        Exec.descendantFrames, List.filterMap_nil] using LedgerMirrors.nil dp ca
  | runOk hstep henter child hresume next ihChild ihNext =>
      rw [Exec.descendantActions_runOk hstep henter child hresume next]
      simp only [Exec.attributionInner]
      refine LedgerMirrors.append ?_ ihNext
      split
      · rename_i hs
        rw [Exec.flowActions_eq_root_append_descendants child
          (Blanc.Weth10.Frame.raw_commits_of_settlementCommits hs)]
        exact LedgerMirrors.frameContribution _ ihChild
      · exact .nil dp ca

/-- The counted stream of a whole derivation mirrors its classified actions. -/
theorem Exec.ledgerMirrors_attributionStream (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    LedgerMirrors dp ca (Exec.attributionStream dp ca run)
      (Exec.flowActions dp ca run) := by
  by_cases hcommits : Execution.commits out = true
  · rw [Exec.attributionStream_eq_frameContribution dp ca run hcommits,
      Exec.flowActions_eq_root_append_descendants run hcommits]
    exact LedgerMirrors.frameContribution _
      (Exec.ledgerMirrors_attributionInner dp ca run)
  · rw [Exec.attributionStream_eq_nil_of_not_commits run hcommits,
      Exec.flowActions_eq_nil_of_not_commits run hcommits]
    exact .nil dp ca

/-! ## The mirror through the retained trace tower -/

theorem RetainedXlot.ledgerMirrors (dp : DeployParams) (ca : Adr)
    {xl : Xlot} (retained : RetainedXlot xl) :
    LedgerMirrors dp ca (retained.attributionStream dp ca)
      (retained.flowActions dp ca) := by
  cases retained with
  | none => exact .nil dp ca
  | some run => exact Exec.ledgerMirrors_attributionStream dp ca run

theorem MessageCallTrace.ledgerMirrors (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    LedgerMirrors dp ca (trace.attributionStream dp ca)
      (trace.flowActions dp ca) := by
  cases trace with
  | createCollision htarget hcollision hresult => exact .nil dp ca
  | createRun htarget hcollision evm hcore trace hresult =>
      simp only [MessageCallTrace.attributionStream,
        MessageCallTrace.flowActions]
      split
      · exact .nil dp ca
      · exact trace.retained.ledgerMirrors dp ca
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      exact trace.retained.ledgerMirrors dp ca

theorem TransactionTrace.ledgerMirrors (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    LedgerMirrors dp ca (trace.attributionStream dp ca)
      (trace.flowActions dp ca) :=
  trace.message.ledgerMirrors dp ca

theorem ApplyTransactionsTrace.ledgerMirrors (dp : DeployParams) (ca : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) →
    LedgerMirrors dp ca (trace.attributionStream dp ca)
      (trace.flowActions dp ca)
  | _, _, _, _, _, .nil _ _ => .nil dp ca
  | _, _, _, _, _, .cons head tail =>
      (head.ledgerMirrors dp ca).append
        (ApplyTransactionsTrace.ledgerMirrors dp ca tail)

theorem SystemMessageTrace.ledgerMirrors (dp : DeployParams) (ca : Adr)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    LedgerMirrors dp ca (trace.attributionStream dp ca)
      (trace.flowActions dp ca) :=
  trace.message.ledgerMirrors dp ca

theorem RequestsTrace.ledgerMirrors (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    LedgerMirrors dp ca (trace.attributionStream dp ca)
      (trace.flowActions dp ca) :=
  (trace.withdrawal.ledgerMirrors dp ca).append
    (trace.consolidation.ledgerMirrors dp ca)

theorem AppliedBodyTrace.ledgerMirrors (dp : DeployParams) (ca : Adr)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    LedgerMirrors dp ca (trace.attributionStream dp ca)
      (trace.flowActions dp ca) :=
  (((trace.beacon.ledgerMirrors dp ca).append
    (trace.history.ledgerMirrors dp ca)).append
      (trace.transactions.ledgerMirrors dp ca)).append
        (trace.requests.ledgerMirrors dp ca)

theorem AccountedBlock.ledgerMirrors
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock chainId dp ca pre post) :
    LedgerMirrors dp ca (accounted.attributionStream dp ca)
      accounted.actions := by
  rw [accounted.actions_eq]
  exact accounted.bodyTrace.ledgerMirrors dp ca

/-- The chronological attribution ledger of a history mirrors its committed
action ledger: every record is retained, and both carry the same permanent
outflow for every holder. -/
theorem AccountedHistory.ledgerMirrors
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    LedgerMirrors dp ca history.attributionLedger history.flowActions := by
  induction history with
  | refl hcfg hctx hid => exact .nil dp ca
  | step prior accounted ih => exact ih.append accounted.ledgerMirrors

/-! ## Reconciliation with the public holder-flow totals -/

/-- The public observation ledger is the deterministic projection of the
retained action ledger. -/
theorem AccountedHistory.flowObservations_eq_map
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    history.flowObservations =
      history.flowActions.map FlowAction.observation := by
  induction history with
  | refl hcfg hctx hid => rfl
  | step prior accounted ih =>
      simp only [AccountedHistory.flowObservations,
        AccountedHistory.flowActions, ih, List.map_append,
        accounted.observations_eq, accounted.actions_eq,
        AppliedBodyTrace.flowObservations]

theorem actionOutflow_eq_holderFlow (u : Adr) (actions : List FlowAction) :
    actionOutflow u actions =
      (holderFlowOfActions actions u).redeemed +
        (holderFlowOfActions actions u).externalTransferredOut := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      have hsplit : holderFlowOfActions (action :: rest) u =
          (action.atom.holderFlow u).add (holderFlowOfActions rest u) := by
        have h := holderFlowOfActions_append [action] rest u
        simpa [holderFlowOfActions] using h
      rw [actionOutflow, ih, hsplit]
      simp only [HolderFlow.add]
      omega

/-- Stage reconciliation: the permanent outflow summed over the chronological
attribution ledger is exactly the public redeemed-plus-transferred-out total
of the holder-flow fold. -/
theorem AccountedHistory.ledgerOutflow_eq_permanentOutflow
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    ledgerOutflow u history.attributionLedger =
      (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut := by
  rw [history.ledgerMirrors.outflow u, actionOutflow_eq_holderFlow]
  unfold AccountedHistory.weth10Flow
  rw [history.flowObservations_eq_map, holderFlowOfObservations_map_observation]

/-! ## Frame-local reconciliation -/

/-- The debit provenance recorded by the two delegated selectors. -/
private def delegatedDebitOf (e : Sevm) (pre : Devm) : DebitProvenance :=
  { actualCaller := e.caller
    rawSource := Sevm.argWord e 0
    source := (Sevm.argWord e 0).toAdr
    branch := .delegated (callerAllowanceBranch e pre 2) }

/-- The debit provenance recorded by the four direct selectors. -/
private def directDebitOf (e : Sevm) : DebitProvenance :=
  { actualCaller := e.caller
    rawSource := e.caller.toB256
    source := e.caller
    branch := .direct }

/-- The allowance visit recorded by the two delegated selectors when the
runtime does not take the raw-word self-bypass. -/
private def spendEventOf (e : Sevm) (pre : Devm) : AllowanceEvent :=
  { owner := Sevm.argWord e 0
    spender := e.caller.toB256
    caller := e.caller
    depth := e.depth
    visit :=
      let before :=
        (Devm.getStor pre e.currentTarget).get (callerAllowanceRuntimeKey e)
      if before = B256.max then .spendMax
      else .spendFinite before (before - Sevm.argWord e 2) }

/-- The allowance key inspected by a delegated debit, if any. -/
def delegatedKey? : DebitBranch → Option B256
  | .delegated (.finite key _ _) => some key
  | .delegated (.maximum key) => some key
  | _ => none

/-- Witness shape produced by the frame-local reconciliation: the debit is
either `u`'s own direct or self-bypass debit, or an allowance-branch debit
keyed at the record's own touched pair, whose owner word normalizes to `u`. -/
def DebitWitness (e : Sevm) (pre post : Devm) (u : Adr)
    (debit : DebitProvenance) : Prop :=
  (debit.branch = .direct ∨ debit.branch = .delegated .selfBypass) ∧
      debit.actualCaller = u ∨
    ∃ event, frameAllowanceEvent e pre post = some event ∧
      event.owner.toAdr = u ∧ delegatedKey? debit.branch = some event.key

/-- The delegated arm shared by `transferFrom` and `withdrawFrom`: the debit's
allowance key is the projected key of the very pair the visit records, so a
debit of `u`'s balance is either the raw-word self-bypass by `u` itself or an
allowance-branch debit at `u`'s own touched pair. -/
private theorem delegated_witness {e : Sevm} {pre post : Devm} {u : Adr}
    (hevent : Sevm.argWord e 0 ≠ e.caller.toB256 →
      frameAllowanceEvent e pre post = some (spendEventOf e pre))
    (hsource : (Sevm.argWord e 0).toAdr = u) :
    DebitWitness e pre post u (delegatedDebitOf e pre) := by
  unfold DebitWitness
  by_cases hself : Sevm.argWord e 0 = e.caller.toB256
  · refine Or.inl ⟨Or.inr ?_, ?_⟩
    · simp [delegatedDebitOf, callerAllowanceBranch, hself]
    · show e.caller = u
      rw [← hsource, hself, toAdr_toB256]
  · refine Or.inr ⟨spendEventOf e pre, hevent hself, hsource, ?_⟩
    simp only [delegatedDebitOf, callerAllowanceBranch, if_neg hself]
    split <;>
      simp [delegatedKey?, spendEventOf, AllowanceEvent.key,
        callerAllowanceRuntimeKey_eq_projected]

/-- Frame-local reconciliation of the three if-chains.  The classified atom,
the debit provenance and the allowance visit of one exact invocation are
computed from the same entry context, so a nonzero permanent outflow for `u`
pins the debit. -/
theorem primaryDebit_witness {e : Sevm} {pre post : Devm} {u : Adr}
    {atom : FlowAtom} (hatom : primaryFlowAtom e = some atom)
    (hout : atom.outflow u ≠ 0) :
    ∃ debit, primaryDebitProvenance e pre post = some debit ∧
      DebitWitness e pre post u debit := by
  simp only [primaryFlowAtom] at hatom
  split_ifs at hatom with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · cases hatom
    simp at hout
  · cases hatom
    simp at hout
  · cases hatom
    simp at hout
  · cases hatom
    have hcaller : e.caller = u :=
      FlowAtom.source_of_outflow_redemption hout
    refine ⟨directDebitOf e, ?_, Or.inl ⟨Or.inl rfl, hcaller⟩⟩
    rcases (by simpa using h4 :
        Sevm.selector e = transferSelector ∨
          Sevm.selector e = transferAndCallSelector) with h | h <;>
      simp [primaryDebitProvenance, directDebitOf, h1, h]
  · cases hatom
    have hcaller : e.caller = u :=
      FlowAtom.source_of_outflow_transfer hout
    refine ⟨directDebitOf e, ?_, Or.inl ⟨Or.inl rfl, hcaller⟩⟩
    rcases (by simpa using h4 :
        Sevm.selector e = transferSelector ∨
          Sevm.selector e = transferAndCallSelector) with h | h <;>
      simp [primaryDebitProvenance, directDebitOf, h1, h]
  · cases hatom
    refine ⟨delegatedDebitOf e pre, ?_,
      delegated_witness ?_ (FlowAtom.source_of_outflow_redemption hout)⟩
    · simp [primaryDebitProvenance, delegatedDebitOf, h1, h6,
        transferFromSelector_ne_transferSelector,
        transferFromSelector_ne_transferAndCallSelector,
        transferFromSelector_ne_withdrawSelector,
        transferFromSelector_ne_withdrawToSelector]
    · intro hself
      simp [frameAllowanceEvent, spendEventOf, h1, h6, hself,
        transferFromSelector_ne_approveSelector,
        transferFromSelector_ne_approveAndCallSelector,
        transferFromSelector_ne_permitSelector]
  · cases hatom
    refine ⟨delegatedDebitOf e pre, ?_,
      delegated_witness ?_ (FlowAtom.source_of_outflow_transfer hout)⟩
    · simp [primaryDebitProvenance, delegatedDebitOf, h1, h6,
        transferFromSelector_ne_transferSelector,
        transferFromSelector_ne_transferAndCallSelector,
        transferFromSelector_ne_withdrawSelector,
        transferFromSelector_ne_withdrawToSelector]
    · intro hself
      simp [frameAllowanceEvent, spendEventOf, h1, h6, hself,
        transferFromSelector_ne_approveSelector,
        transferFromSelector_ne_approveAndCallSelector,
        transferFromSelector_ne_permitSelector]
  · cases hatom
    have hcaller : e.caller = u :=
      FlowAtom.source_of_outflow_redemption hout
    refine ⟨directDebitOf e, ?_, Or.inl ⟨Or.inl rfl, hcaller⟩⟩
    simp [primaryDebitProvenance, directDebitOf, h1, h8]
  · cases hatom
    have hcaller : e.caller = u :=
      FlowAtom.source_of_outflow_redemption hout
    refine ⟨directDebitOf e, ?_, Or.inl ⟨Or.inl rfl, hcaller⟩⟩
    simp [primaryDebitProvenance, directDebitOf, h1, h9]
  · cases hatom
    refine ⟨delegatedDebitOf e pre, ?_,
      delegated_witness ?_ (FlowAtom.source_of_outflow_redemption hout)⟩
    · simp [primaryDebitProvenance, delegatedDebitOf, h1, h10,
        withdrawFromSelector_ne_transferSelector,
        withdrawFromSelector_ne_transferAndCallSelector,
        withdrawFromSelector_ne_withdrawSelector,
        withdrawFromSelector_ne_withdrawToSelector,
        withdrawFromSelector_ne_transferFromSelector]
    · intro hself
      simp [frameAllowanceEvent, spendEventOf, h1, h10, hself,
        withdrawFromSelector_ne_approveSelector,
        withdrawFromSelector_ne_approveAndCallSelector,
        withdrawFromSelector_ne_permitSelector]
  · cases hatom
    simp at hout

/-- The classified action of a frame carries exactly the deterministic atom
and debit computed from that frame's entry context. -/
theorem Exec.Frame.flowAction?_inv {dp : DeployParams} {ca : Adr}
    {frame : Exec.Frame} {action : FlowAction}
    (haction : frame.flowAction? dp ca = some action) :
    primaryFlowAtom frame.sevm = some action.atom ∧
      action.debit =
        primaryDebitProvenance frame.sevm frame.pre frame.post := by
  unfold Exec.Frame.flowAction? at haction
  split at haction
  · cases hatom : primaryFlowAtom frame.sevm with
    | none => rw [hatom] at haction; exact absurd haction (by simp)
    | some atom =>
        rw [hatom] at haction
        cases haction
        exact ⟨rfl, rfl⟩
  · exact absurd haction (by simp)

/-- Only the `approve` arm records an `approveStore` visit, and that arm's
owner word is the clean `CALLER` word of the visiting frame. -/
theorem frameAllowanceEvent_approveStore_owner {e : Sevm} {pre post : Devm}
    {event : AllowanceEvent} {value : B256}
    (hevent : frameAllowanceEvent e pre post = some event)
    (hvisit : event.visit = .approveStore value) :
    event.owner = event.caller.toB256 := by
  simp only [frameAllowanceEvent] at hevent
  split_ifs at hevent <;> cases hevent <;>
    first
      | rfl
      | simp at hvisit

/-- A delegated debit is hardened as soon as its inspected allowance key is
attributed to the holder. -/
theorem hardenedFor_of_delegatedKey {debit : DebitProvenance}
    {recent : List CountedFrame} {u : Adr} {key : B256}
    (hkey : delegatedKey? debit.branch = some key)
    (hroot : (attributionRootAt recent key).attributedTo u = true) :
    debit.hardenedFor recent u = true := by
  revert hkey
  unfold DebitProvenance.hardenedFor delegatedKey?
  cases debit.branch with
  | direct => simp
  | delegated allowance =>
      cases allowance with
      | selfBypass => simp
      | finite k before after => intro hkey; cases hkey; exact hroot
      | maximum k => intro hkey; cases hkey; exact hroot
  | flash allowance =>
      cases allowance with
      | selfBypass => simp
      | finite k before after => simp
      | maximum k => simp

/-! ## The trace-local collision step -/

/-- The pairwise non-collision relation of `NoAllowanceKeyCollision`. -/
def NoCollisionRel (p q : B256 × B256) : Prop :=
  p ≠ q → projectedAllowanceKey p.1 p.2 ≠ projectedAllowanceKey q.1 q.2

/-- The raw word pairs hashed by a counted ledger, in trace order. -/
def touchedPairs (ledger : List CountedFrame) : List (B256 × B256) :=
  ledger.filterMap fun record =>
    record.allowance.map fun event => (event.owner, event.spender)

theorem touchedAllowancePairs_eq_touchedPairs
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    touchedAllowancePairs history = touchedPairs history.attributionLedger :=
  rfl

theorem mem_touchedPairs {ledger : List CountedFrame} {p : B256 × B256} :
    p ∈ touchedPairs ledger ↔
      ∃ record ∈ ledger, ∃ event, record.allowance = some event ∧
        p = (event.owner, event.spender) := by
  simp only [touchedPairs, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨record, hrecord, event, hevent, hp⟩
    exact ⟨record, hrecord, event, hevent, hp.symm⟩
  · rintro ⟨record, hrecord, event, hevent, hp⟩
    exact ⟨record, hrecord, event, hevent, hp.symm⟩

theorem touchedPairs_append (left right : List CountedFrame) :
    touchedPairs (left ++ right) =
      touchedPairs left ++ touchedPairs right := by
  simp only [touchedPairs, List.filterMap_append]

/-- The attribution root of a key is the checkpoint, or the approve/permit
record of a counted frame whose own visit hashed to that very key. -/
theorem attributionRootAt_cases (recent : List CountedFrame) (key : B256) :
    attributionRootAt recent key = .checkpoint ∨
      ∃ record ∈ recent, ∃ event, record.allowance = some event ∧
        event.key = key ∧
        ((∃ value, event.visit = .approveStore value) ∧
            attributionRootAt recent key = .approve event.caller ∨
          (∃ value, event.visit = .permitStore value) ∧
            attributionRootAt recent key = .permit event.owner) := by
  induction recent with
  | nil => exact Or.inl rfl
  | cons record rest ih =>
      cases hallowance : record.allowance with
      | none =>
          rw [show attributionRootAt (record :: rest) key =
            attributionRootAt rest key by
              simp only [attributionRootAt, hallowance]]
          rcases ih with h | ⟨other, hother, event, hevent, hkey, hroot⟩
          · exact Or.inl h
          · exact Or.inr ⟨other, List.mem_cons_of_mem _ hother, event,
              hevent, hkey, hroot⟩
      | some event =>
          by_cases hkey : event.key = key
          · cases hvisit : event.visit with
            | approveStore value =>
                refine Or.inr ⟨record, List.mem_cons_self, event,
                  hallowance, hkey, Or.inl ⟨⟨value, hvisit⟩, ?_⟩⟩
                simp only [attributionRootAt, hallowance, hvisit, if_pos hkey]
            | permitStore value =>
                refine Or.inr ⟨record, List.mem_cons_self, event,
                  hallowance, hkey, Or.inr ⟨⟨value, hvisit⟩, ?_⟩⟩
                simp only [attributionRootAt, hallowance, hvisit, if_pos hkey]
            | _ =>
                rw [show attributionRootAt (record :: rest) key =
                  attributionRootAt rest key by
                    simp only [attributionRootAt, hallowance, hvisit,
                      if_pos hkey]]
                rcases ih with h | ⟨other, hother, ev, hev, hk, hroot⟩
                · exact Or.inl h
                · exact Or.inr ⟨other, List.mem_cons_of_mem _ hother, ev,
                    hev, hk, hroot⟩
          · rw [show attributionRootAt (record :: rest) key =
              attributionRootAt rest key by
                simp only [attributionRootAt, hallowance, if_neg hkey]]
            rcases ih with h | ⟨other, hother, ev, hev, hk, hroot⟩
            · exact Or.inl h
            · exact Or.inr ⟨other, List.mem_cons_of_mem _ hother, ev, hev,
                hk, hroot⟩

/-- **The collision step.**  A retained record's hardened contribution is its
whole permanent outflow, provided no other retained pair of the recent stream
hashes to this record's own projected allowance key.

This is the single point at which trace-local collision freedom is consumed.
An allowance-branch debit of holder `u` reads the key projected from the pair
`(rawSource, caller)` its own visit recorded; the governing store found by
`attributionRootAt` wrote the key projected from that store's own recorded
pair.  Equal keys therefore force equal pairs, so an `approve` root's clean
`CALLER` owner word and a `permit` root's recovered owner word both normalize
to `u`.  Direct debits, the raw-word self-bypass and flash settlement need no
such reasoning: the first two are `u`'s own act, and a flash pair contributes
no permanent outflow at all. -/
theorem CountedFrame.hardenedContribution_eq_permanentOutflow
    {dp : DeployParams} {ca : Adr} (u : Adr)
    {record : CountedFrame} {recent : List CountedFrame}
    (horigin : record.HasFrameOrigin dp ca)
    (hrecent : ∀ other ∈ recent, other.HasFrameOrigin dp ca)
    (hcross : ∀ p ∈ touchedPairs recent, ∀ q ∈ touchedPairs [record],
      NoCollisionRel p q) :
    record.hardenedContribution recent u = record.permanentOutflow u := by
  rcases horigin with ⟨frame, rfl⟩
  by_cases hout : (CountedFrame.ofFrame dp ca frame).permanentOutflow u = 0
  · have hle := (CountedFrame.ofFrame dp ca frame).hardenedContribution_le
      recent u
    omega
  · obtain ⟨action, haction⟩ :
        ∃ action,
          (CountedFrame.ofFrame dp ca frame).action = some action := by
      cases haction : (CountedFrame.ofFrame dp ca frame).action with
      | none =>
          exact absurd
            (by rw [CountedFrame.permanentOutflow_eq, haction]) hout
      | some action => exact ⟨action, rfl⟩
    have hatomout : action.atom.outflow u ≠ 0 := by
      rw [CountedFrame.permanentOutflow_eq, haction] at hout
      exact hout
    obtain ⟨hprimary, hdebiteq⟩ :=
      Exec.Frame.flowAction?_inv (dp := dp) (ca := ca) haction
    obtain ⟨debit, hdebit, hwitness⟩ :=
      primaryDebit_witness (pre := frame.pre) (post := frame.post)
        hprimary hatomout
    have hactiondebit : action.debit = some debit := by
      rw [hdebiteq, hdebit]
    have hhard : debit.hardenedFor recent u = true := by
      rcases hwitness with ⟨hbranch, hcaller⟩ |
        ⟨event, hevent, howner, hkey⟩
      · unfold DebitProvenance.hardenedFor
        rcases hbranch with hb | hb <;> rw [hb] <;> simpa using hcaller
      · refine hardenedFor_of_delegatedKey hkey ?_
        rcases attributionRootAt_cases recent event.key with
          hroot | ⟨other, hother, ev, hev, hevkey, hcase⟩
        · rw [hroot]
          rfl
        · have hpair :
              (ev.owner, ev.spender) = (event.owner, event.spender) := by
            by_contra hne
            exact hcross (ev.owner, ev.spender)
              (mem_touchedPairs.mpr ⟨other, hother, ev, hev, rfl⟩)
              (event.owner, event.spender)
              (mem_touchedPairs.mpr
                ⟨CountedFrame.ofFrame dp ca frame, List.mem_cons_self,
                  event, hevent, rfl⟩)
              hne hevkey
          have hownerEq : ev.owner = event.owner := congrArg Prod.fst hpair
          rcases hcase with ⟨⟨value, hvisit⟩, hroot⟩ |
            ⟨⟨value, hvisit⟩, hroot⟩
          · rcases hrecent other hother with ⟨otherFrame, rfl⟩
            have hclean : ev.owner = ev.caller.toB256 :=
              frameAllowanceEvent_approveStore_owner hev hvisit
            have hcaller : ev.caller = u := by
              rw [← toAdr_toB256 ev.caller, ← hclean, hownerEq, howner]
            rw [hroot]
            simpa [AttributionRoot.attributedTo] using hcaller
          · rw [hroot]
            simpa [AttributionRoot.attributedTo] using
              (hownerEq ▸ howner : ev.owner.toAdr = u)
    simp only [CountedFrame.hardenedContribution, haction, hactiondebit,
      hhard, if_true]

/-! ## The unconditional bound -/

/-- The hardened sub-sum never exceeds the permanent outflow.  No collision
hypothesis, stability, or execution authenticity is involved: every counted
record's hardened contribution is bounded by its own permanent outflow. -/
theorem hardenedOutflow_le_permanentOutflow
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    hardenedOutflow history u ≤
      (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut := by
  rw [← history.ledgerOutflow_eq_permanentOutflow]
  unfold hardenedOutflow
  generalize history.attributionLedger = ledger
  generalize ([] : List CountedFrame) = recent
  induction ledger generalizing recent with
  | nil => exact Nat.le_refl 0
  | cons frame rest ih =>
      exact Nat.add_le_add (frame.hardenedContribution_le recent u) (ih _)

/-! ## The collision-free equality -/

theorem mem_touchedPairs_reverse {ledger : List CountedFrame}
    {p : B256 × B256} :
    p ∈ touchedPairs ledger.reverse ↔ p ∈ touchedPairs ledger := by
  rw [mem_touchedPairs, mem_touchedPairs]
  simp only [List.mem_reverse]

/-- Under trace-local collision freedom every counted debit of holder `u`'s
balance carries a hardened attribution witness, so the hardened sub-sum is the
whole permanent outflow.  The collision hypothesis is consumed only by
`CountedFrame.hardenedContribution_eq_permanentOutflow`, one record at a time.

The checkpoint-stability premise is retained for interface compatibility with
the surrounding redeemability development and is deliberately unused: the
attribution root of a debit is read off the chronological ledger itself, so no
allowance value has to be transported from the checkpoint. -/
theorem permanentOutflow_eq_hardenedOutflow_of_noCollision
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (_hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history) :
    (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut =
      hardenedOutflow history u := by
  have horigins := history.ledgerMirrors.origins
  have hpairs :
      (touchedPairs history.attributionLedger).Pairwise NoCollisionRel := by
    rw [← touchedAllowancePairs_eq_touchedPairs history]
    exact hnc
  rw [← history.ledgerOutflow_eq_permanentOutflow]
  unfold hardenedOutflow
  revert horigins hpairs
  generalize history.attributionLedger = ledger
  intro horigins hpairs
  generalize hnil : ([] : List CountedFrame) = recent
  have hrecentOrigins :
      ∀ record ∈ recent, record.HasFrameOrigin dp ca := by
    rw [← hnil]; simp
  have hall :
      (touchedPairs (recent.reverse ++ ledger)).Pairwise NoCollisionRel := by
    rw [← hnil]; simpa using hpairs
  clear hnil hpairs
  revert horigins hrecentOrigins hall
  induction ledger generalizing recent with
  | nil => intro _ _ _; rfl
  | cons record rest ih =>
      intro horigins hrecentOrigins hall
      have hsplit : (touchedPairs recent.reverse ++
          touchedPairs (record :: rest)).Pairwise NoCollisionRel := by
        rw [← touchedPairs_append]
        exact hall
      obtain ⟨-, -, hcross⟩ := List.pairwise_append.mp hsplit
      have hhead :
          record.hardenedContribution recent u = record.permanentOutflow u := by
        refine CountedFrame.hardenedContribution_eq_permanentOutflow u
          (horigins record (by simp)) hrecentOrigins ?_
        intro p hp q hq
        refine hcross p (mem_touchedPairs_reverse.mpr hp) q ?_
        rcases mem_touchedPairs.mp hq with
          ⟨other, hother, event, hevent, hq⟩
        rw [List.mem_singleton] at hother
        exact mem_touchedPairs.mpr
          ⟨other, by simp [hother], event, hevent, hq⟩
      have hlist : (record :: recent).reverse ++ rest =
          recent.reverse ++ (record :: rest) := by simp
      rw [show ledgerOutflow u (record :: rest) =
        record.permanentOutflow u + ledgerOutflow u rest from rfl, ← hhead,
        ih (recent := record :: recent)
          (fun other hother => horigins other (List.mem_cons_of_mem _ hother))
          (fun other hother => by
            rcases List.mem_cons.mp hother with rfl | h
            · exact horigins other (by simp)
            · exact hrecentOrigins other h)
          (by rw [hlist]; exact hall)]
      rfl

end Weth10

end Blanc
