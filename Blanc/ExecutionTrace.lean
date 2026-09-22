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
        simpa using
          (exec_iff_exec_eq evm.pc evm.sta evm.dyna raw).mp filled
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

/-- The collision test used by the create arm of `processMessageCall`. -/
def messageCreateCollision (msg : Msg) : Bool :=
  accountHasCodeOrNonce msg.benv.state msg.currentTarget ||
    accountHasStorage msg.benv.state msg.currentTarget

/-- The exact EIP-7702 preparation prefix used by the call arm. -/
def messageCallDelegation (msg : Msg) : Except EvmError (Msg × Nat) :=
  if msg.tenv.stat.auths.isEmpty then
    .ok ⟨msg, 0⟩
  else do
    let ⟨delegated, refund⟩ ← setDelegation msg
    .ok ⟨delegated, refund.toNat⟩

/-- The actual message executed after resolving an EIP-7702 code delegation. -/
def messageCallExecutionMessage (msg : Msg) : Msg :=
  match getDelegatedCodeAddress msg.code with
  | none => msg
  | some dca =>
      { msg with
        disablePrecompiles := true
        accessedAddresses := msg.accessedAddresses.insert dca
        code := msg.benv.state.getCode dca
        codeAddress := some dca }

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
theorem exists_messageCallTrace {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨state, out⟩)
    (hfork : CoveredFork msg.benv.stat.fork) :
    Nonempty (MessageCallTrace msg state out) := by
  have h_result := h
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  unfold processMessageCall at h
  split at h
  · rename_i htarget
    unfold processMessageCall.create at h
    rw [hsg] at h
    dsimp only at h
    split at h
    · rename_i hcollision
      exact ⟨.createCollision htarget (by
        simpa [messageCreateCollision] using hcollision) h_result⟩
    · rename_i hcollision
      obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
      have hcore := Except.bimap_id_eq_ok hevm
      rcases exists_processCreateMessageTrace msg (.ok evm) hcore with
        ⟨trace⟩
      exact ⟨.createRun htarget (by
        simpa [messageCreateCollision] using hcollision)
        evm hcore trace h_result⟩
  · rename_i htarget
    have htargetFalse : msg.target.isNone = false := by
      cases ht : msg.target.isNone <;> simp_all
    unfold processMessageCall.call at h
    rw [hsg] at h
    dsimp only at h
    split at h
    · rename_i hauth
      obtain ⟨x0, hx0, h⟩ := Except.bind_eq_ok h
      cases hx0
      dsimp only at h
      split at h
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore :
            processMessage (messageCallExecutionMessage msg) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse msg 0 (by
          simp [messageCallDelegation, hauth])
          (messageCallExecutionMessage msg) rfl evm hcore trace h_result⟩
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore :
            processMessage (messageCallExecutionMessage msg) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse msg 0 (by
          simp [messageCallDelegation, hauth])
          (messageCallExecutionMessage msg) rfl evm hcore trace h_result⟩
    · rename_i hauth
      obtain ⟨w, hw, h⟩ := Except.bind_eq_ok h
      obtain ⟨delegated, refundWord⟩ := w
      obtain ⟨x0, hx0, h⟩ := Except.bind_eq_ok h
      cases hx0
      dsimp only at h
      split at h
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore : processMessage
            (messageCallExecutionMessage delegated) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse delegated refundWord.toNat (by
          unfold messageCallDelegation
          rw [if_neg hauth, hw]
          rfl)
          (messageCallExecutionMessage delegated) rfl evm hcore trace h_result⟩
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore : processMessage
            (messageCallExecutionMessage delegated) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse delegated refundWord.toNat (by
          unfold messageCallDelegation
          rw [if_neg hauth, hw]
          rfl)
          (messageCallExecutionMessage delegated) rfl evm hcore trace h_result⟩

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
          .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
        accessListStorageKeys :=
          .ofList (tx.accessList.map (fun ⟨adr, keys⟩ =>
            keys.map (⟨adr, ·⟩))).flatten
        blobVersionedHashes := blobVersionedHashes
        auths := tx.auths
        indexInBlock := index
        txHash := getTxHash tx } }

/-- Intrinsic-cost sender independence in the none lane: the only `sender`
use in `calculateIntrinsicCost` is the some-lane recipient check, so
covered-fork validation results agree for any recovery address. This is what
lets transaction traces record the opaque `validationSender` without
replaying Jaune-private sender recovery. -/
private lemma calculateIntrinsicCost_sender_congr_none {rules : ForkRules}
    {tx : Tx} {s1 s2 : Adr} (hsg : rules.stateGas = none) :
    calculateIntrinsicCost rules tx s1 = calculateIntrinsicCost rules tx s2 := by
  unfold calculateIntrinsicCost
  rw [hsg]

/-- None-lane validation agrees for any recovery address. -/
private lemma validateTransaction_sender_congr_none {rules : ForkRules}
    {tx : Tx} {s1 s2 : Adr} (hsg : rules.stateGas = none) :
    validateTransaction rules tx s1 = validateTransaction rules tx s2 := by
  unfold validateTransaction
  rw [hsg]
  rw [calculateIntrinsicCost_sender_congr_none hsg]

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

/-- Every successful transaction admits an exact retained message trace. -/
theorem exists_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (h : processTransaction benv bout tx index = .ok (state, bout'))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (TransactionTrace benv bout tx index state bout') := by
  have h_result := h
  have hsg : benv.stat.fork.ruleSet.stateGas = none := by
    simpa [BenvStat.rules] using hfork.rules_stateGas_none
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
  have hfork_msg : CoveredFork msg.benv.stat.fork := by
    rw [prepareMessage_benv_stat_fork hprepared]
    exact hfork
  rcases exists_messageCallTrace hmessage hfork_msg with ⟨messageTrace⟩
  exact ⟨⟨validationSender, intrinsicGas, calldataFloorGasCost, sender,
    effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, debitState,
    msg, messageState, messageOut,
    by simpa [Benv.beginTransaction, BenvStat.rules] using hvalidated,
    by simpa [transactionPreludeBout] using hchecked,
    by simpa [transactionBlobGasFee, Benv.beginTransaction, BenvStat.rules] using hdebit',
    by
      simpa [transactionTenv, Benv.beginTransaction, BenvStat.rules,
        allocateEvmGas, hsg] using hprepared,
    messageTrace, h_result⟩⟩

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
  simp only [BenvStat.rules] at hsg
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
    have hsg : benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
    have hcong : validateTransaction benv.stat.rules tx validationSender =
        validateTransaction benv.stat.rules tx trace.validationSender :=
      validateTransaction_sender_congr_none hsg
    have hvalidated' : validateTransaction benv.stat.rules tx validationSender =
        .ok ⟨intrinsicGas, calldataFloorGasCost⟩ := by
      simpa [BenvStat.rules] using hvalidated
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
      (by simpa [transactionBlobGasFee, BenvStat.rules] using trace.debit))
  subst debitState
  rcases Except.bind_eq_ok hrun with ⟨msg, hprepared, hrun⟩
  simp only [allocateEvmGas, hsg] at hprepared
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
  simp only [settleTransactionGas, settleSelfdestructs, hsg] at hrun
  have hfinal := Except.ok.inj hrun
  exact ⟨refundCounter, hrefundSome, (Prod.mk.inj hfinal).1.symm⟩

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
private theorem applyTransactionsTrace_stat_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    finalBenv.stat = benv.stat := by
  induction trace with
  | nil => rfl
  | cons _ tail ih => simpa [Benv.withState] using ih

theorem exists_applyTransactionsTrace
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (h : applyTransactions txs benv bout = .ok (finalBenv, finalBout))
    (hfork : CoveredFork benv.stat.fork) :
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
      rcases exists_transactionTrace htx hfork with ⟨headTrace⟩
      have hfork_tail : CoveredFork (benv.withState txState).stat.fork :=
        hfork
      rcases ih htail hfork_tail with ⟨tailTrace⟩
      exact ⟨.cons headTrace tailTrace⟩

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

theorem exists_systemMessageTrace
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (h : processUncheckedSystemTransaction benv target data =
      .ok (state, out))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (SystemMessageTrace benv target data state out) := by
  have hmessage : processMessageCall
      (systemTransactionMessage benv target data) = .ok (state, out) := by
    simpa [processUncheckedSystemTransaction, processSystemTransaction,
      systemTransactionMessage] using h
  have hfork_msg :
      CoveredFork (systemTransactionMessage benv target data).benv.stat.fork := by
    unfold systemTransactionMessage processSystemTransactionMsg
      Benv.beginTransaction
    exact hfork
  rcases exists_messageCallTrace hmessage hfork_msg with ⟨trace⟩
  exact ⟨⟨trace, h⟩⟩

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
    rcases hfork with hfork | hfork
    · rw [hfork]
      exact pragueRules_requests
    · rw [hfork]
      rfl
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at h
  obtain ⟨deposits, hdeposits, h⟩ := Except.bind_eq_ok h
  rw [hrequests] at h
  cases hwithdrawal : processCheckedSystemTransaction benv
      withdrawalRequestPredeployAddress [] with
  | error err =>
      have impossible : False := by
        simp [runRequestContracts, Except.bind, bind, hwithdrawal] at h
      exact impossible.elim
  | ok withdrawal =>
      cases hconsolidation : processCheckedSystemTransaction
          (benv.withState withdrawal.1)
          consolidationRequestPredeployAddress [] with
      | error err =>
          have impossible : False := by
            simp [runRequestContracts, Except.bind, bind, hwithdrawal,
              hconsolidation] at h
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
          stat := benv.stat }
        consolidationRequestPredeployAddress [] =
          .ok (trace.consolidationState, trace.consolidationOut) := by
    simpa only [Benv.withState] using trace.consolidationRun
  have hrun := trace.run
  have hconsolidation' := trace.consolidationRun
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at hrun
  rw [trace.parsed] at hrun
  rw [trace.requestShape] at hrun
  simp [runRequestContracts, Except.bind, bind, trace.withdrawalRun,
    hconsolidation'] at hrun
  simpa [Benv.withState] using hrun.1.symm

/-- Complete retained execution evidence for a successful body under Jaune's
currently modelled body semantics.  This includes the two pre-transaction
system calls, every decoded normal transaction, and the two checked
request-system calls. -/
structure AppliedBodyTrace (benv : Benv) (txs : List (Bytes ⊕ Tx))
    (wds : List Withdrawal) (state : State) (bout : BlockOutput) where
  run : applyBody benv txs wds = .ok (state, bout)
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
  decodeRun : txs.mapM decodeTx = .ok decodedTxs
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
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    state = trace.requests.consolidationState :=
  trace.requestState_eq.symm.trans
    trace.requests.state_eq_consolidationState
theorem exists_appliedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (h : applyBody benv txs wds = .ok (state, bout))
    (hfork : CoveredFork benv.stat.fork) :
    Nonempty (AppliedBodyTrace benv txs wds state bout) := by
  have h_result := h
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  rw [applyBody] at h
  simp only [BalBuilder.incorporateSystem, hbal,
    checkBlockAccessListGasLimit] at h
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
  dsimp [processWithdrawals] at hrequests
  rcases Except.bind_eq_ok hrequests with
    ⟨⟨requestState, requestBout⟩, hrequests, hfinal⟩
  have hfork_requests : CoveredFork
      (transactionBenv.withState
        (processWithdrawalsState transactionBenv.state wds)).stat.fork := by
    have hfork_transactions : CoveredFork transactionBenv.stat.fork := by
      rw [applyTransactionsTrace_stat_eq transactionsTrace]
      exact hfork
    simpa [Benv.withState] using hfork_transactions
  rcases exists_requestsTrace hrequests hfork_requests with ⟨requestsTrace⟩
  have hfinal' : requestState = state ∧
      {requestBout with blockAccessList := []} = bout := by
    simpa [Except.bind, bind] using hfinal
  exact ⟨⟨h_result, beaconState, beaconOut, beaconTrace,
    lastHash, hlastHash, historyState, historyOut, historyTrace,
    decodedTxs, hdecoded, transactionBenv, transactionBout,
    transactionsTrace, requestState, requestBout, requestsTrace,
    hfinal'.1, hfinal'.2⟩⟩

end ExecutionTrace

end Blanc
