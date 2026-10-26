import Blanc.ExecutionCommittedCell
import Blanc.ExecutionRetainedNoDelTransaction

/-! Exact protected-account code and cell at actual complete-settlement root entries. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- A retained slot's outer root begins after the actual frame entry transfer.
The transfer preserves nonempty-code storage and every code image. -/
theorem RetainedXlot.settledRoots_entry_getCode_getStor
    {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (process : RunFrame frame slot out) {wa : Adr}
    (nonempty : (frame.inner.benv.state.getCode wa).toList ≠ []) :
    ∀ R ∈ retained.settledRoots,
      R.pre.getCode wa = frame.inner.benv.state.getCode wa ∧
      R.pre.getStor wa = frame.inner.benv.state.getStor wa := by
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [RetainedXlot.settledRoots] at member
    split at member
    · rw [List.mem_singleton] at member
      subst R
      exact ⟨Frame.enter_run_getCode (RunFrame.some_inv process).1 wa,
        Frame.enter_run_getStor (RunFrame.some_inv process).1 wa nonempty⟩
    · cases member

/-- Complete CALL settlement selects only the root of this actual message. -/
theorem ProcessMessageTrace.settledRoots_entry_getCode_getStor
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) {wa : Adr}
    (nonempty : (msg.benv.state.getCode wa).toList ≠ []) :
    ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = msg.benv.state.getCode wa ∧
      R.pre.getStor wa = msg.benv.state.getStor wa := by
  rcases trace with ⟨slot, retained, process⟩
  have entry := retained.settledRoots_entry_getCode_getStor process nonempty
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · exact entry R member
    · cases member

/-- A complete CREATE root preserves the original protected account at entry;
its target seeding cannot alter another nonempty-code account. -/
theorem ProcessCreateMessageTrace.settledRoots_entry_getCode_getStor
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) {wa : Adr}
    (nonempty : (msg.benv.state.getCode wa).toList ≠ [])
    (target : msg.currentTarget ≠ wa) :
    ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = msg.benv.state.getCode wa ∧
      R.pre.getStor wa = msg.benv.state.getStor wa := by
  rcases trace with ⟨slot, retained, process⟩
  have innerCode : (Frame.ofCreate msg).inner.benv.state.getCode wa =
      msg.benv.state.getCode wa := processCreateMessage.msg_getCode msg wa
  have entry := retained.settledRoots_entry_getCode_getStor process
    (by rw [innerCode]; exact nonempty)
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · obtain ⟨code, storage⟩ := entry R member
      exact ⟨code.trans innerCode, storage.trans (createEntry_getStor target)⟩
    · cases member

/-- Authorization, resolved code and CREATE entry preserve the protected cell
before this same message's settled root; no execution invariant is assumed. -/
theorem MessageCallTrace.settledRoots_entry_code_cell
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) {wa : Adr} {C : ByteArray}
    (installed : msg.benv.state.getCode wa = C)
    (nonempty : C.toList ≠ []) (notDelegation : ¬ isValidDelegation C) (key : B256) :
    ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = C ∧
      (R.pre.getStor wa).get key = (msg.benv.state.getStor wa).get key := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun target collision evm core retained result =>
    have targetNe : msg.currentTarget ≠ wa :=
      ne_wa_of_not_hasCodeOrNonce (by rw [installed]; exact nonempty)
        (by simpa only [messageCreateCollision] using collision)
    intro R member
    obtain ⟨code, storage⟩ := retained.settledRoots_entry_getCode_getStor
      (by rw [installed]; exact nonempty) targetNe R member
    exact ⟨code.trans installed, congrArg (fun s : Stor => s.get key) storage⟩
  | callRun target delegated refund delegation execMsg execution evm core retained result =>
    have entryCode : execMsg.benv.state.getCode wa = C := by
      rw [execution, messageCallExecutionMessage_getCode]
      exact delegation_keeps_code_entry delegation installed nonempty notDelegation
    intro R member
    obtain ⟨code, storage⟩ := retained.settledRoots_entry_getCode_getStor
      (by rw [entryCode]; exact nonempty) R member
    exact ⟨code.trans entryCode,
      (congrArg (fun s : Stor => s.get key) storage).trans
        (execMsg_cell_eq execution delegation installed nonempty notDelegation key)⟩

/-- The actual transaction's nonce and fee debit preserve the cell and code
used by its same retained root. This is not a claim about descendant entries. -/
theorem TransactionTrace.settledRoots_entry_code_cell
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {wa : Adr} {C : ByteArray} (installed : benv.state.getCode wa = C)
    (nonempty : C.toList ≠ []) (notDelegation : ¬ isValidDelegation C) (key : B256) :
    ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = C ∧
      (R.pre.getStor wa).get key = (benv.state.getStor wa).get key := by
  have prepared := prepareMessage_benv trace.prepared
  have debitCode : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have entryCode : trace.msg.benv.state.getCode wa = C := by
    rw [prepared]
    exact debitCode.trans installed
  have entryCell : (trace.msg.benv.state.getStor wa).get key =
      (benv.state.getStor wa).get key := by
    rw [prepared]
    exact congrArg (fun storage : Stor => storage.get key)
      (TransactionTrace.debitState_getStor_eq trace)
  intro R member
  obtain ⟨code, cell⟩ := trace.message.settledRoots_entry_code_cell
    entryCode nonempty notDelegation key R member
  exact ⟨code, cell.trans entryCell⟩


/-- Couple the selected cell with deletion exclusion at the actual transaction.
Every root callback receives its derived entry code and cell property first. -/
theorem TransactionTrace.cell_noDel_of_settledRoots
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {wa : Adr} {C : ByteArray} (key : B256)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C)
    (nonempty : C.toList ≠ []) (notDelegation : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (property : B256 → Prop)
    (roots : ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = C → property ((R.pre.getStor wa).get key) →
      (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧
        property ((R.post.getStor wa).get key))
    (initial : property ((benv.state.getStor wa).get key)) :
    wa ∉ trace.messageOut.accountsToDelete ∧
      property ((state.getStor wa).get key) ∧ state.getCode wa = C ∧
      ∀ R ∈ trace.settledRoots,
        R.pre.getCode wa = C ∧ property ((R.pre.getStor wa).get key) := by
  have ready : ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = C ∧ property ((R.pre.getStor wa).get key) := by
    intro R member
    obtain ⟨code, cell⟩ := trace.settledRoots_entry_code_cell
      installed nonempty notDelegation key R member
    exact ⟨code, by rw [cell]; exact initial⟩
  have noDel := trace.noDel_of_settledRoots notDelegation nonempty hsg installed notCreated
    (fun R member => (roots R member (ready R member).1 (ready R member).2).1)
  have cell := trace.cell_property_of_settledRoots key hsg installed nonempty notDelegation
    noDel.1 property
    (fun R member _ => (roots R member (ready R member).1 (ready R member).2).2) initial
  exact ⟨noDel.1, cell.1, cell.2, ready⟩

/-- The coupled code/cell/deletion invariant passes through the actual ordered
transaction list, retaining entry evidence for every original settled root. -/
theorem ApplyTransactionsTrace.cell_noDel_of_settledRoots
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {wa : Adr} {C : ByteArray} (key : B256)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C)
    (nonempty : C.toList ≠ []) (notDelegation : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (property : B256 → Prop)
    (roots : ∀ R ∈ trace.settledRoots,
      R.pre.getCode wa = C → property ((R.pre.getStor wa).get key) →
      (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧
        property ((R.post.getStor wa).get key))
    (initial : property ((benv.state.getStor wa).get key)) :
    trace.NoDelScheduled wa ∧ property ((finalBenv.state.getStor wa).get key) ∧
      finalBenv.state.getCode wa = C ∧
      ∀ R ∈ trace.settledRoots,
        R.pre.getCode wa = C ∧ property ((R.pre.getStor wa).get key) := by
  induction trace with
  | nil => exact ⟨trivial, initial, installed, by intro R member; cases member⟩
  | cons head tail ih =>
    have headResult := head.cell_noDel_of_settledRoots key hsg installed nonempty
      notDelegation notCreated property
      (fun R member => roots R (List.mem_append_left _ member)) initial
    have tailResult := ih hsg headResult.2.2.1 notCreated
      (fun R member => roots R (List.mem_append_right _ member)) headResult.2.1
    refine ⟨⟨headResult.1, tailResult.1⟩, tailResult.2.1, tailResult.2.2.1, ?_⟩
    intro R member
    rcases List.mem_append.mp member with earlier | later
    · exact headResult.2.2.2 R earlier
    · exact tailResult.2.2.2 R later


/-- A disabled opening beacon stage leaves the actual entry state unchanged. -/
theorem BeaconStageTrace.state_eq_of_disabled
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (disabled : rules.sys.beaconRoots = false) : state = benv.state := by
  cases trace with
  | skipped => rfl
  | called enabled _ _ _ _ => rw [disabled] at enabled; cases enabled

/-- A disabled opening history stage leaves the actual entry state unchanged. -/
theorem HistoryStageTrace.state_eq_of_disabled
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder}
    {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (disabled : rules.sys.historyStorage = false) : state = benv.state := by
  cases trace with
  | skipped => rfl
  | called enabled _ _ _ _ _ _ => rw [disabled] at enabled; cases enabled

end Blanc.ExecutionTrace
