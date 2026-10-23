import Blanc.ExecutionSettlement

/-!
Contract-neutral retained traces for successful EVM message, transaction, and
the currently modelled Jaune block-body execution.  These carriers preserve
the exact recursive executions selected by Jaune's deterministic wrappers
without assigning any contract-specific observations to them.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace


/-- A Type-valued version of a filled recursive execution slot.  Unlike
`Xlot.Filled`, this retains the concrete `Exec` value that the accounting fold
and its successor provenance analysis consume. -/
inductive RetainedXlot : Xlot → Type
  | none : RetainedXlot .none
  | some {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) :
      RetainedXlot (.some ⟨⟨pc, sevm, pre⟩, out⟩)

theorem RetainedXlot.toFilled {xl : Xlot} : RetainedXlot xl → xl.Filled
  | .none => trivial
  | .some run => ⟨run⟩

theorem exists_retainedXlot_of_filled {xl : Xlot}
    (h : xl.Filled) : Nonempty (RetainedXlot xl) := by
  cases xl with
  | none => exact ⟨.none⟩
  | some slot =>
      rcases slot with ⟨evm, out⟩
      rcases h with ⟨run⟩
      exact ⟨.some run⟩

/-- A retained recursive slot pins the executable result selected by a frame.
Kept private because the public consumers are the two exact trace carriers
below. -/
private theorem runFrame_result_of_retained
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot)
    (run : RunFrame frame slot out) :
    runFrame frame = out := by
  cases henter : frame.enter with
  | done result =>
      simp only [RunFrame, henter] at run
      unfold runFrame
      rw [henter]
      exact run.2.symm
  | run evm =>
      simp only [RunFrame, henter] at run
      rcases run with ⟨raw, slotEq, resultEq⟩
      have filled := retained.toFilled
      rw [slotEq] at filled
      simp only [Xlot.Filled] at filled
      have execResult : exec evm = raw := by
        simpa only using (exec_iff_exec_eq evm.pc evm.sta evm.dyna raw).mp filled
      unfold runFrame
      rw [henter]
      simp only
      rw [execResult]
      exact resultEq.symm

/-- An exact retained execution of Jaune's raw call-message core. -/
structure ProcessMessageTrace (msg : Msg)
    (out : Except (EvmError × State × AdrSet × Tra) Devm) where
  slot : Xlot
  retained : RetainedXlot slot
  run : ProcessMessage msg slot out

theorem exists_processMessageTrace
    (msg : Msg) (out : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : processMessage msg = out) :
    Nonempty (ProcessMessageTrace msg out) := by
  obtain ⟨xl, hfilled, hrun⟩ := of_processMessage msg out h
  rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
  exact ⟨⟨xl, retained, hrun⟩⟩

/-- Recover the exact deterministic `processMessage` equation retained by the
trace. -/
theorem ProcessMessageTrace.result
    {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) :
    processMessage msg = out := by
  simpa only [processMessage] using
    (runFrame_result_of_retained trace.retained trace.run)

/-- An exact retained execution of Jaune's raw create-message core. -/
structure ProcessCreateMessageTrace (msg : Msg)
    (out : Except (EvmError × State × AdrSet × Tra) Devm) where
  slot : Xlot
  retained : RetainedXlot slot
  run : ProcessCreateMessage msg slot out

theorem exists_processCreateMessageTrace
    (msg : Msg) (out : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : processCreateMessage msg = out) :
    Nonempty (ProcessCreateMessageTrace msg out) := by
  obtain ⟨xl, hfilled, hrun⟩ := of_processCreateMessage msg out h
  rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
  exact ⟨⟨xl, retained, hrun⟩⟩

/-- Recover the exact deterministic `processCreateMessage` equation retained
by the trace. -/
theorem ProcessCreateMessageTrace.result
    {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    processCreateMessage msg = out := by
  simpa only [processCreateMessage] using
    (runFrame_result_of_retained trace.retained trace.run)

/-- The collision test used by the create arm of `processMessageCall`: EIP-684
only. EIP-7610's storage clause is withdrawn upstream, so an account holding
only storage is deployable and its storage is wiped on entry. -/
def messageCreateCollision (msg : Msg) : Bool :=
  accountHasCodeOrNonce msg.benv.state msg.currentTarget

/-- The exact fork-gated authorization prefix used by the call arm. -/
def messageCallDelegation (msg : Msg) : Except EvmError (Msg × Nat) :=
  processMessageCall.legacyAuthorization msg

/-- The actual message executed after fork-gated code delegation resolution. -/
def messageCallExecutionMessage (msg : Msg) : Msg :=
  msg.resolveCodeDelegation

/-- Proof-carrying trace of Jaune's settled message-call wrapper.  The three
constructors match its collision, create-execution, and call-execution arms;
the retained core is tied to the exact deterministic wrapper result. -/
inductive MessageCallTrace (msg : Msg) (state : State)
    (out : MsgCallOutput) : Type
  | createCollision
      (h_target : msg.target.isNone = true)
      (h_collision : messageCreateCollision msg = true)
      (h_result : processMessageCall msg = .ok ⟨state, out⟩) :
      MessageCallTrace msg state out
  | createRun
      (h_target : msg.target.isNone = true)
      (h_collision : messageCreateCollision msg = false)
      (evm : Devm)
      (h_core : processCreateMessage msg = .ok evm)
      (trace : ProcessCreateMessageTrace msg (.ok evm))
      (h_result : processMessageCall msg = .ok ⟨state, out⟩) :
      MessageCallTrace msg state out
  | callRun
      (h_target : msg.target.isNone = false)
      (delegated : Msg) (refund : Nat)
      (h_delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
      (execMsg : Msg)
      (h_execMsg : execMsg = messageCallExecutionMessage delegated)
      (evm : Devm)
      (h_core : processMessage execMsg = .ok evm)
      (trace : ProcessMessageTrace execMsg (.ok evm))
      (h_result : processMessageCall msg = .ok ⟨state, out⟩) :
      MessageCallTrace msg state out
/-- Every successful settled message-call wrapper admits a retained trace of
the exact raw execution core it ran. -/
theorem exists_messageCallTrace_of_stateGas_none {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨state, out⟩)
    (hsg : msg.benv.stat.rules.stateGas = none) :
    Nonempty (MessageCallTrace msg state out) := by
  have h_result := h
  unfold processMessageCall at h
  split at h
  · rename_i htarget
    unfold processMessageCall.create at h
    rw [hsg] at h
    dsimp only at h
    split at h
    · rename_i hcollision
      exact ⟨.createCollision htarget (by
        simpa only [messageCreateCollision, Bool.or_eq_true] using hcollision) h_result⟩
    · rename_i hcollision
      obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
      have hcore := Except.bimap_id_eq_ok hevm
      rcases exists_processCreateMessageTrace msg (.ok evm) hcore with
        ⟨trace⟩
      exact ⟨.createRun htarget (by
        simpa only [messageCreateCollision, Bool.or_eq_false_iff, Bool.or_eq_true, not_or,
          Bool.not_eq_true] using hcollision)
        evm hcore trace h_result⟩
  · rename_i htarget
    have htargetFalse : msg.target.isNone = false := by
      cases ht : msg.target.isNone <;> simp_all only [Bool.false_eq_true, not_false_eq_true, Option.isNone_eq_false_iff, not_true_eq_false]
    unfold processMessageCall.call at h
    rw [hsg] at h
    dsimp only at h
    obtain ⟨⟨delegated, refund⟩, hdelegated, h⟩ := Except.bind_eq_ok h
    obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
    have hcore : processMessage (messageCallExecutionMessage delegated) = .ok evm :=
      Except.bimap_id_eq_ok hevm
    rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
    exact ⟨.callRun htargetFalse delegated refund hdelegated
      (messageCallExecutionMessage delegated) rfl evm hcore trace h_result⟩

/-- Compatibility with the existing covered-fork extraction interface. -/
theorem exists_messageCallTrace {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨state, out⟩)
    (hfork : CoveredFork msg.benv.stat.fork) :
    Nonempty (MessageCallTrace msg state out) := by
  exact exists_messageCallTrace_of_stateGas_none h hfork.rules_stateGas_none

/-- Recover the exact deterministic wrapper equation retained by a message
trace. -/
theorem MessageCallTrace.result
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    processMessageCall msg = .ok (state, out) := by
  cases trace <;> assumption

/-! ## Transaction traces -/

def transactionPreludeBout
    (bout : BlockOutput) (tx : Tx) (index : Nat) : BlockOutput :=
  { bout with
    transactionsTrie := bout.transactionsTrie.insert
      (BLT.bytes index.toBytes).toBytes tx }

def transactionBlobGasFee (benv : Benv) (tx : Tx) : Nat :=
  if tx.isTypeThree then
    calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
  else 0

def transactionTenv (benv : Benv) (tx : Tx) (index : Nat)
    (sender : Adr) (effectiveGasPrice intrinsicGas : Nat)
    (blobVersionedHashes : List B256) : Tenv :=
  { transientStorage := .empty
    stat :=
      { origin := sender
        gasPrice := effectiveGasPrice
        gas := tx.gas - intrinsicGas
        accessListAddresses :=
          if benv.stat.rules.txr.warmCoinbase then
            .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
          else .ofList (tx.accessList.map Prod.fst)
        accessListStorageKeys :=
          .ofList (tx.accessList.map (fun ⟨adr, keys⟩ =>
            keys.map (⟨adr, ·⟩))).flatten
        blobVersionedHashes := blobVersionedHashes
        auths := tx.auths
        indexInBlock := index
        txHash := getTxHash tx } }

/-- Prepared messages keep their builder's fork: `prepareMessage` fixes
`benv` into the message untouched. -/
private lemma prepareMessage_benv_stat_fork {benv : Benv} {tenv : Tenv}
    {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.benv.stat.fork = benv.stat.fork := by
  unfold prepareMessage at h
  split at h <;> dsimp only at h <;>
    (obtain rfl := Except.ok.inj h; rfl)

/-- A successful transaction together with the exact prepared message and its
retained recursive execution.  Validation, sender recovery/fee checking,
up-front debit, and message preparation are all replay equations, so an
unrelated or forged message trace cannot inhabit this type.

`validationSender` is recorded opaquely: Jaune-private sender recovery cannot
be named from Blanc, but none-lane validation is sender-independent
(`validateTransaction_sender_congr_none`), so the equation still pins the gas
pair at covered forks. -/
structure TransactionTrace (benv : Benv) (bout : BlockOutput)
    (tx : Tx) (index : Nat) (state : State) (bout' : BlockOutput) where
  validationSender : Adr
  intrinsicGas : Nat
  calldataFloorGasCost : Nat
  sender : Adr
  effectiveGasPrice : Nat
  blobVersionedHashes : List B256
  txBlobGasUsed : Nat
  debitState : State
  msg : Msg
  messageState : State
  messageOut : MsgCallOutput
  validation : validateTransaction benv.stat.rules tx validationSender =
    .ok (intrinsicGas, calldataFloorGasCost)
  checked : checkTransaction benv.beginTransaction
    (transactionPreludeBout bout tx index) tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed)
  debit : (benv.state.incrNonce sender).subBal sender
    (tx.gas * effectiveGasPrice +
      transactionBlobGasFee benv tx).toB256 = some debitState
  prepared : prepareMessage
    { benv.beginTransaction with state := debitState }
    (transactionTenv benv.beginTransaction tx index sender
      effectiveGasPrice intrinsicGas blobVersionedHashes) tx = .ok msg
  message : MessageCallTrace msg messageState messageOut
  result : processTransaction benv bout tx index = .ok (state, bout')
  /-- The validation sender is the one Jaune's `processTransaction` recovers:
  `0` on the no-state-gas lane, otherwise the chain-id-checked recovered
  signer.  Stated with the public components of Jaune's private
  `recoverValidationSender`, so the trace is determined by its inputs. -/
  validationSender_run :
    (match benv.beginTransaction.stat.rules.stateGas with
      | none => Except.ok 0
      | some _ => do
        Except.mapError TransitionError.transaction
          (checkTransactionChainId benv.beginTransaction tx)
        Except.mapError (fun e => TransitionError.senderRecovery e)
          (recoverSender benv.beginTransaction.stat.chainId tx) :
      Except TransitionError Adr) = .ok validationSender

/-- Every successful transaction admits an exact retained message trace. -/
theorem exists_transactionTrace_of_stateGas_none
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (h : processTransaction benv bout tx index = .ok (state, bout'))
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (TransactionTrace benv bout tx index state bout') := by
  have h_result := h
  have hsg_rules : benv.stat.fork.ruleSet.stateGas = none := by
    simpa only [BenvStat.rules] using hsg
  unfold processTransaction at h
  dsimp only at h
  obtain ⟨prelude, hprelude, h⟩ := Except.bind_eq_ok h
  cases hprelude
  obtain ⟨validationSender, hrec, h⟩ := Except.bind_eq_ok h
  obtain ⟨validated, hvalidated, h⟩ := Except.bind_eq_ok h
  obtain ⟨intrinsicGas, calldataFloorGasCost⟩ := validated
  rw [Except.mapError_eq_ok_iff] at hvalidated
  obtain ⟨checked, hchecked, h⟩ := Except.bind_eq_ok h
  obtain ⟨sender, effectiveGasPrice, blobVersionedHashes,
    txBlobGasUsed⟩ := checked
  obtain ⟨debitState, hdebit, h⟩ := Except.bind_eq_ok h
  have hdebit' := Option.toExcept_eq_ok hdebit
  obtain ⟨msg, hprepared, h⟩ := Except.bind_eq_ok h
  obtain ⟨messageResult, hmessage, _⟩ := Except.bind_eq_ok h
  obtain ⟨messageState, messageOut⟩ := messageResult
  rw [Except.mapError_eq_ok_iff] at hmessage
  have hsg_msg : msg.benv.stat.rules.stateGas = none := by
    change msg.benv.stat.fork.ruleSet.stateGas = none
    rw [prepareMessage_benv_stat_fork hprepared]
    exact hsg
  rcases exists_messageCallTrace_of_stateGas_none hmessage hsg_msg with
    ⟨messageTrace⟩
  exact ⟨⟨validationSender, intrinsicGas, calldataFloorGasCost, sender,
    effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, debitState,
    msg, messageState, messageOut,
    by simpa only [BenvStat.rules, Benv.beginTransaction] using hvalidated,
    by simpa only [transactionPreludeBout] using hchecked,
    by simpa only [transactionBlobGasFee, BenvStat.rules, Benv.beginTransaction] using hdebit',
    by
      simpa only [Benv.beginTransaction, transactionTenv, Std.TreeMap.empty_eq_emptyc,
        allocateEvmGas, BenvStat.rules, hsg_rules] using hprepared,
    messageTrace, h_result, hrec⟩⟩

/-- Compatibility with the existing covered-fork extraction interface. -/
theorem exists_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (h : processTransaction benv bout tx index = .ok (state, bout'))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (TransactionTrace benv bout tx index state bout') := by
  exact exists_transactionTrace_of_stateGas_none h hfork.rules_stateGas_none

/-- Selected final-state form under the actual `stateGas = none` condition.
The gas/refund/coinbase expressions call the semantic `settleTransactionGas`
with the trace's retained fields, so the selected quotient and validated floor
flow through it; the touched sweep stays symbolic. -/
theorem TransactionTrace.exists_selectedFinalStateForm
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    ∃ refundCounter : Nat,
      Int.toNat? trace.messageOut.refundCounter = some refundCounter ∧
      state =
        sweepTouchedAccounts benv.stat.rules trace.messageOut.touchedAccounts.toList
          (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
            ((trace.messageState.addBal trace.sender
              (((settleTransactionGas benv.stat.rules tx.gas trace.calldataFloorGasCost
                trace.messageOut.gasLeft trace.messageOut.stateGasLeft
                refundCounter trace.messageOut.stateGasUsed).gasLeft *
                trace.effectiveGasPrice).toB256)).addBal
              benv.stat.coinbase
                (((settleTransactionGas benv.stat.rules tx.gas trace.calldataFloorGasCost
                  trace.messageOut.gasLeft trace.messageOut.stateGasLeft
                  refundCounter trace.messageOut.stateGasUsed).gasUsed *
                  (trace.effectiveGasPrice -
                    benv.stat.baseFeePerGas)).toB256))) := by
  have hsg_fork : benv.stat.fork.ruleSet.stateGas = none := by
    simpa only [BenvStat.rules] using hsg
  have hrun := trace.result
  unfold processTransaction at hrun
  simp only [Benv.beginTransaction, BenvStat.rules] at hrun
  rcases Except.bind_eq_ok hrun with ⟨prelude, hprelude, hrun⟩
  have hpreludeEq := Except.ok.inj hprelude
  subst prelude
  rcases Except.bind_eq_ok hrun with ⟨validationSender, hrec, hrun⟩
  rcases Except.bind_eq_ok hrun with ⟨validated, hvalidated, hrun⟩
  rcases validated with ⟨intrinsicGas, calldataFloorGasCost⟩
  rw [Except.mapError_eq_ok_iff] at hvalidated
  have hvalidatedEq : intrinsicGas = trace.intrinsicGas ∧
      calldataFloorGasCost = trace.calldataFloorGasCost := by
    have hcong : validateTransaction benv.stat.rules tx validationSender =
        validateTransaction benv.stat.rules tx trace.validationSender :=
      validateTransaction_sender_congr_none hsg
    have hvalidated' : validateTransaction benv.stat.rules tx validationSender =
        .ok ⟨intrinsicGas, calldataFloorGasCost⟩ := by
      simpa only [BenvStat.rules] using hvalidated
    rw [hcong] at hvalidated'
    exact Prod.mk.inj (Except.ok.inj (hvalidated'.symm.trans trace.validation))
  rcases hvalidatedEq with ⟨rfl, rfl⟩
  rcases Except.bind_eq_ok hrun with ⟨checked, hchecked, hrun⟩
  rcases checked with
    ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  have hcheckedEq := Except.ok.inj (hchecked.symm.trans trace.checked)
  simp only [Prod.mk.injEq] at hcheckedEq
  rcases hcheckedEq with ⟨rfl, rfl, rfl, rfl⟩
  rcases Except.bind_eq_ok hrun with ⟨debitState, hdebit, hrun⟩
  have hdebitSome := Option.toExcept_eq_ok hdebit
  have hdebitEq : debitState = trace.debitState := by
    exact Option.some.inj (hdebitSome.symm.trans
      (by simpa only [transactionBlobGasFee, BenvStat.rules] using trace.debit))
  subst debitState
  rcases Except.bind_eq_ok hrun with ⟨msg, hprepared, hrun⟩
  simp only [allocateEvmGas, hsg_fork] at hprepared
  have htracePrepared := trace.prepared
  simp only [transactionTenv, Benv.beginTransaction] at htracePrepared
  have hmsgEq : msg = trace.msg := Except.ok.inj
    (hprepared.symm.trans htracePrepared)
  subst msg
  rcases Except.bind_eq_ok hrun with ⟨messageResult, hmessage, hrun⟩
  rcases messageResult with ⟨messageState, messageOut⟩
  rw [Except.mapError_eq_ok_iff] at hmessage
  have htraceMessage : processMessageCall trace.msg =
      .ok (trace.messageState, trace.messageOut) :=
    trace.message.result
  have hmessageEq : messageState = trace.messageState ∧
      messageOut = trace.messageOut := by
    exact Prod.mk.inj (Except.ok.inj
      (hmessage.symm.trans htraceMessage))
  rcases hmessageEq with ⟨rfl, rfl⟩
  rcases Except.bind_eq_ok hrun with ⟨refundCounter, hrefund, hrun⟩
  have hrefundSome := Option.toExcept_eq_ok hrefund
  simp only [settleSelfdestructs, hsg_fork] at hrun
  have hfinal := Except.ok.inj hrun
  refine ⟨refundCounter, hrefundSome, ?_⟩
  simpa only [BenvStat.rules] using (Prod.mk.inj hfinal).1.symm

/-- Exact post-message transaction settlement form.  This exposes the two
gas credits and the final account-deletion fold without re-executing or
approximating the transaction. -/
theorem TransactionTrace.exists_finalStateForm
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) :
    ∃ refundCounter : Nat,
      Int.toNat? trace.messageOut.refundCounter = some refundCounter ∧
      state =
        trace.messageOut.accountsToDelete.toList.foldl destroyAccount
          ((trace.messageState.addBal trace.sender
              ((tx.gas -
                  max (tx.gas - trace.messageOut.gasLeft -
                    min ((tx.gas - trace.messageOut.gasLeft) / 5)
                      refundCounter)
                    trace.calldataFloorGasCost) *
                trace.effectiveGasPrice).toB256).addBal
            benv.stat.coinbase
              (max (tx.gas - trace.messageOut.gasLeft -
                  min ((tx.gas - trace.messageOut.gasLeft) / 5)
                    refundCounter)
                  trace.calldataFloorGasCost *
                (trace.effectiveGasPrice -
                  benv.stat.baseFeePerGas)).toB256) := by
  have hsg : benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  rcases trace.exists_selectedFinalStateForm hsg with
    ⟨refundCounter, hrefund, hfinal⟩
  have hrefundQuotient : benv.stat.fork.ruleSet.settle.refundQuotient = 5 :=
    hfork.cases (motive := fun f => f.ruleSet.settle.refundQuotient = 5) rfl rfl rfl rfl
  have hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false :=
    hfork.cases (motive := fun f => f.ruleSet.settle.touchedSweep = false) rfl rfl rfl rfl
  have hsg_fork : benv.stat.fork.ruleSet.stateGas = none := by
    simpa only [BenvStat.rules] using hsg
  refine ⟨refundCounter, hrefund, ?_⟩
  simpa only [settleTransactionGas, sweepTouchedAccounts, BenvStat.rules, hsg_fork,
    hrefundQuotient, hsweep, Bool.false_eq_true, ↓reduceIte] using hfinal

/-- Exact retained replay of the decoded transaction list. -/
inductive ApplyTransactionsTrace :
    List (Nat × Tx) → Benv → BlockOutput → Benv → BlockOutput → Type
  | nil (benv : Benv) (bout : BlockOutput) :
      ApplyTransactionsTrace [] benv bout benv bout
  | cons {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput}
      {txState : State} {txBout : BlockOutput}
      {finalBenv : Benv} {finalBout : BlockOutput}
      (head : TransactionTrace benv bout tx index txState txBout)
      (tail : ApplyTransactionsTrace txs (benv.withState txState) txBout
        finalBenv finalBout) :
      ApplyTransactionsTrace ((index, tx) :: txs) benv bout
        finalBenv finalBout

/-- A transaction fold changes only its state component of `Benv`.  This
local form is kept beside the carrier so compatibility construction can carry
fork evidence through the fold without importing downstream accounting APIs. -/
theorem ApplyTransactionsTrace.stat_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    finalBenv.stat = benv.stat := by
  induction trace with
  | nil => rfl
  | cons _ tail ih => simpa only [Benv.withState] using ih

/-- The transaction list the trace retains is exactly the one the semantics
ran, so every list-level ladder rung applies to a trace unchanged. -/
theorem ApplyTransactionsTrace.run
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    applyTransactions txs benv bout = .ok (finalBenv, finalBout) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      rw [applyTransactions, head.result]
      exact ih

theorem exists_applyTransactionsTrace_of_stateGas_none
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (h : applyTransactions txs benv bout = .ok (finalBenv, finalBout))
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (ApplyTransactionsTrace txs benv bout finalBenv finalBout) := by
  induction txs generalizing benv bout with
  | nil =>
      simp only [applyTransactions] at h
      cases h
      exact ⟨.nil finalBenv finalBout⟩
  | cons head txs ih =>
      obtain ⟨index, tx⟩ := head
      simp only [applyTransactions] at h
      obtain ⟨txResult, htx, htail⟩ := Except.bind_eq_ok h
      obtain ⟨txState, txBout⟩ := txResult
      rcases exists_transactionTrace_of_stateGas_none htx hsg with ⟨headTrace⟩
      have hsg_tail : (benv.withState txState).stat.rules.stateGas = none :=
        hsg
      rcases ih htail hsg_tail with ⟨tailTrace⟩
      exact ⟨.cons headTrace tailTrace⟩

/-- Compatibility with the existing covered-fork extraction interface. -/
theorem exists_applyTransactionsTrace
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (h : applyTransactions txs benv bout = .ok (finalBenv, finalBout))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (ApplyTransactionsTrace txs benv bout finalBenv finalBout) := by
  exact exists_applyTransactionsTrace_of_stateGas_none h hfork.rules_stateGas_none

/-! ## System-message and body traces -/

def systemTransactionMessage
    (benv : Benv) (target : Adr) (data : Bytes) : Msg :=
  let active := benv.beginTransaction
  processSystemTransactionMsg active (processSystemTransactionTenv active)
    target data (benv.state.getCode target)

/-- Exact retained root for one unchecked system transaction. -/
structure SystemMessageTrace (benv : Benv) (target : Adr) (data : Bytes)
    (state : State) (out : MsgCallOutput) where
  message : MessageCallTrace
    (systemTransactionMessage benv target data) state out
  run : processUncheckedSystemTransaction benv target data = .ok (state, out)

theorem exists_systemMessageTrace_of_stateGas_none
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (h : processUncheckedSystemTransaction benv target data =
      .ok (state, out))
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (SystemMessageTrace benv target data state out) := by
  have hmessage : processMessageCall
      (systemTransactionMessage benv target data) = .ok (state, out) := by
    simpa only [systemTransactionMessage, processUncheckedSystemTransaction,
      processSystemTransaction] using h
  have hsg_msg :
      (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    unfold systemTransactionMessage processSystemTransactionMsg
      Benv.beginTransaction
    exact hsg
  rcases exists_messageCallTrace_of_stateGas_none hmessage hsg_msg with ⟨trace⟩
  exact ⟨⟨trace, h⟩⟩

/-- Compatibility with the existing covered-fork extraction interface. -/
theorem exists_systemMessageTrace
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (h : processUncheckedSystemTransaction benv target data =
      .ok (state, out))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (SystemMessageTrace benv target data state out) := by
  exact exists_systemMessageTrace_of_stateGas_none h hfork.rules_stateGas_none

/-- Retained execution evidence for the two checked request-system calls at
the tail of `applyBody` on the covered legacy-request lane. -/
structure RequestsTrace (benv : Benv) (bout : BlockOutput)
    (state : State) (bout' : BlockOutput) where
  depositRequests : Bytes
  parsed : parseDepositRequests bout = .ok depositRequests
  requestShape : benv.stat.rules.requests =
    [(1, withdrawalRequestPredeployAddress),
     (2, consolidationRequestPredeployAddress)]
  withdrawalState : State
  withdrawalOut : MsgCallOutput
  withdrawalRun : processCheckedSystemTransaction benv
    withdrawalRequestPredeployAddress [] =
      .ok (withdrawalState, withdrawalOut)
  withdrawal : SystemMessageTrace benv
    withdrawalRequestPredeployAddress [] withdrawalState withdrawalOut
  consolidationState : State
  consolidationOut : MsgCallOutput
  consolidationRun : processCheckedSystemTransaction
    (benv.withState withdrawalState)
    consolidationRequestPredeployAddress [] =
      .ok (consolidationState, consolidationOut)
  consolidation : SystemMessageTrace (benv.withState withdrawalState)
    consolidationRequestPredeployAddress []
    consolidationState consolidationOut
  run : processGeneralPurposeRequests benv bout = .ok (state, bout')
theorem exists_requestsTrace
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (h : processGeneralPurposeRequests benv bout = .ok (state, bout'))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (RequestsTrace benv bout state bout') := by
  have h_result := h
  have hrequests : benv.stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := by
    change (Fork.ruleSet benv.stat.fork).requests = _
    exact hfork.requests_eq
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at h
  obtain ⟨deposits, hdeposits, h⟩ := Except.bind_eq_ok h
  rw [hrequests] at h
  cases hwithdrawal : processCheckedSystemTransaction benv
      withdrawalRequestPredeployAddress [] with
  | error err =>
      have impossible : False := by
        simp only [bind, Except.bind, runRequestContracts, hwithdrawal, reduceCtorEq] at h
      exact impossible.elim
  | ok withdrawal =>
      cases hconsolidation : processCheckedSystemTransaction
          (benv.withState withdrawal.1)
          consolidationRequestPredeployAddress [] with
      | error err =>
          have impossible : False := by
            simp only [bind, Except.bind, runRequestContracts, hwithdrawal, hconsolidation,
              reduceCtorEq] at h
          exact impossible.elim
      | ok consolidation =>
          obtain ⟨withdrawalState, withdrawalOut⟩ := withdrawal
          obtain ⟨consolidationState, consolidationOut⟩ := consolidation
          have hwithdrawal' :=
            processCheckedSystemTransaction_to_unchecked hwithdrawal
          rcases exists_systemMessageTrace hwithdrawal' hfork with
            ⟨withdrawalTrace⟩
          have hconsolidation' :=
            processCheckedSystemTransaction_to_unchecked hconsolidation
          rcases exists_systemMessageTrace hconsolidation' hfork with
            ⟨consolidationTrace⟩
          exact ⟨⟨deposits, hdeposits, hrequests,
            withdrawalState, withdrawalOut, hwithdrawal, withdrawalTrace,
            consolidationState, consolidationOut,
            hconsolidation, consolidationTrace, h_result⟩⟩

/-- The final request-processing state is the state returned by the second
checked system message. -/
theorem RequestsTrace.state_eq_consolidationState
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    state = trace.consolidationState := by
  have hconsolidation :
      processCheckedSystemTransaction
        { state := trace.withdrawalState
          createdAccounts := benv.createdAccounts
          stat := benv.stat
          storageWrites := benv.storageWrites }
        consolidationRequestPredeployAddress [] =
          .ok (trace.consolidationState, trace.consolidationOut) := by
    simpa only [Benv.withState] using trace.consolidationRun
  have hrun := trace.run
  have hconsolidation' := trace.consolidationRun
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at hrun
  rw [trace.parsed] at hrun
  rw [trace.requestShape] at hrun
  simp only [bind, Except.bind, runRequestContracts, trace.withdrawalRun, hconsolidation',
    gt_iff_lt, List.cons_append, List.nil_append, Benv.withState_stat, Except.ok.injEq,
    Prod.mk.injEq] at hrun
  simpa only [Benv.withState] using hrun.1.symm

/-- Complete retained execution evidence for a successful body under Jaune's
currently modelled body semantics.  This includes the two pre-transaction
system calls, every decoded normal transaction, and the two checked
request-system calls. -/
structure AppliedBodyTrace (benv : Benv) (txs : List (Bytes ⊕ Tx))
    (ommers : List Header) (wds : List Withdrawal) (state : State) (bout : BlockOutput) where
  run : applyBody benv txs ommers wds = .ok (state, bout)
  beaconState : State
  beaconOut : MsgCallOutput
  beacon : SystemMessageTrace benv beaconRootsAddress
    benv.stat.parentBeaconBlockRoot.toBytes beaconState beaconOut
  lastHash : B256
  lastHashRun :
    ((benv.withState beaconState).stat.blockHashes.getLast?).toExcept
      (TransitionError.internal
        (.invariant (.text "block hashes is empty"))) = .ok lastHash
  historyState : State
  historyOut : MsgCallOutput
  history : SystemMessageTrace (benv.withState beaconState)
    historyStorageAddress lastHash.toBytes historyState historyOut
  decodedTxs : List Tx
  decodeRun : txs.mapM (decodeTx benv.stat.rules) = .ok decodedTxs
  transactionBenv : Benv
  transactionBout : BlockOutput
  transactions : ApplyTransactionsTrace decodedTxs.putIndex
    ((benv.withState beaconState).withState historyState) .init
    transactionBenv transactionBout
  /-- The request pass itself precedes `applyBody`'s final, legacy-empty
  block-access-list assignment.  Keep both endpoints rather than identifying
  the two `BlockOutput` records by an unproved structural equality. -/
  requestState : State
  requestBout : BlockOutput
  requests : RequestsTrace
    (transactionBenv.withState
      (processWithdrawalsState transactionBenv.state wds))
    (transactionBout.withWithdrawalsTrie
      (processWithdrawalsTrie transactionBout.withdrawalsTrie wds))
    requestState requestBout
  requestState_eq : requestState = state
  requestBout_eq : {requestBout with blockAccessList := []} = bout

/-- The final body state is the second checked request message's state; the
only post-request body operation in the covered legacy lane normalizes the
block access-list output. -/
theorem AppliedBodyTrace.state_eq_consolidationState
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) :
    state = trace.requests.consolidationState :=
  trace.requestState_eq.symm.trans
    trace.requests.state_eq_consolidationState
theorem exists_appliedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (h : applyBody benv txs ommers wds = .ok (state, bout))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (AppliedBodyTrace benv txs ommers wds state bout) := by
  have h_result := h
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  have hbeaconRules : benv.stat.rules.sys.beaconRoots = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistoryRules : benv.stat.rules.sys.historyStorage = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  have hwithdrawalsRules : benv.stat.rules.header.withdrawalsRoot = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.withdrawalsRoot = true) rfl rfl rfl rfl
  have hrequestsRules : benv.stat.rules.header.requestsHash = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  have hpow : benv.stat.rules.pow = none :=
    hfork.cases (motive := fun f => f.ruleSet.pow = none) rfl rfl rfl rfl
  rw [applyBody] at h
  simp only [beaconRootsCall, historyStorageCall, withdrawalsPass, requestsPass,
    hbeaconRules, hhistoryRules, hwithdrawalsRules, hrequestsRules, hpow, ↓reduceIte,
    BalBuilder.incorporateSystem, hbal, checkBlockAccessListGasLimit, bind_assoc] at h
  simp only [bind, Except.bind] at h
  rcases Except.bind_eq_ok h with
    ⟨⟨beaconState, beaconOut⟩, hbeacon, h⟩
  rcases Except.bind_eq_ok h with ⟨lastHash, hlastHash, h⟩
  rcases Except.bind_eq_ok h with
    ⟨⟨historyState, historyOut⟩, hhistory, h⟩
  rcases Except.bind_eq_ok h with ⟨decodedTxs, hdecoded, h⟩
  rcases Except.bind_eq_ok h with
    ⟨⟨transactionBenv, transactionBout⟩, htransactions, hrequests⟩
  dsimp only at hhistory htransactions hrequests
  rw [Except.mapError_eq_ok_iff] at hbeacon hhistory
  rcases exists_systemMessageTrace hbeacon hfork with ⟨beaconTrace⟩
  rcases exists_systemMessageTrace hhistory hfork with ⟨historyTrace⟩
  rcases exists_applyTransactionsTrace htransactions hfork with
    ⟨transactionsTrace⟩
  dsimp only [processWithdrawals] at hrequests
  rcases Except.bind_eq_ok hrequests with
    ⟨⟨requestState, requestBout⟩, hrequests, hfinal⟩
  have hfork_requests : CoveredFork
      (transactionBenv.withState
        (processWithdrawalsState transactionBenv.state wds)).stat.fork := by
    have hfork_transactions : CoveredFork transactionBenv.stat.fork := by
      rw [transactionsTrace.stat_eq]
      exact hfork
    simpa only [Benv.withState] using hfork_transactions
  rcases exists_requestsTrace hrequests hfork_requests with ⟨requestsTrace⟩
  have hfinal' : requestState = state ∧
      {requestBout with blockAccessList := []} = bout := by
    simpa only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] using hfinal
  exact ⟨⟨h_result, beaconState, beaconOut, beaconTrace,
    lastHash, hlastHash, historyState, historyOut, historyTrace,
    decodedTxs, hdecoded, transactionBenv, transactionBout,
    transactionsTrace, requestState, requestBout, requestsTrace,
    hfinal'.1, hfinal'.2⟩⟩

theorem AppliedBodyTrace.decodedTxs_nil {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) (htxs : txs = []) :
    trace.decodedTxs = [] := by
  have hdecode : txs.mapM (decodeTx benv.stat.rules) = .ok [] := by rw [htxs]; rfl
  exact Except.ok.inj (trace.decodeRun.symm.trans hdecode)

theorem AppliedBodyTrace.decodedTxs_of_mapM {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) {l : List Tx}
    (h : txs.mapM (decodeTx benv.stat.rules) = .ok l) : trace.decodedTxs = l :=
  Except.ok.inj (trace.decodeRun.symm.trans h)

end ExecutionTrace

end Blanc
