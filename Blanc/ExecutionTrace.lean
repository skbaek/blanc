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
    (h : processMessageCall msg = .ok ⟨state, out⟩) :
    Nonempty (MessageCallTrace msg state out) := by
  have h_result := h
  unfold processMessageCall at h
  split at h
  · rename_i htarget
    unfold processMessageCall.create at h
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

/-- A successful transaction together with the exact prepared message and its
retained recursive execution.  Validation, sender recovery/fee checking,
up-front debit, and message preparation are all replay equations, so an
unrelated or forged message trace cannot inhabit this type. -/
structure TransactionTrace (benv : Benv) (bout : BlockOutput)
    (tx : Tx) (index : Nat) (state : State) (bout' : BlockOutput) where
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
  validation : validateTransaction benv.stat.rules tx =
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
    (h : processTransaction benv bout tx index = .ok (state, bout')) :
    Nonempty (TransactionTrace benv bout tx index state bout') := by
  have h_result := h
  unfold processTransaction at h
  dsimp only at h
  obtain ⟨prelude, hprelude, h⟩ := Except.bind_eq_ok h
  cases hprelude
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
  rcases exists_messageCallTrace hmessage with ⟨messageTrace⟩
  exact ⟨⟨intrinsicGas, calldataFloorGasCost, sender,
    effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, debitState,
    msg, messageState, messageOut,
    by simpa [Benv.beginTransaction] using hvalidated,
    by simpa [transactionPreludeBout] using hchecked,
    by simpa [transactionBlobGasFee, Benv.beginTransaction] using hdebit',
    by simpa [transactionTenv, Benv.beginTransaction] using hprepared,
    messageTrace, h_result⟩⟩

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
theorem exists_applyTransactionsTrace
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (h : applyTransactions txs benv bout = .ok (finalBenv, finalBout)) :
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
      rcases exists_transactionTrace htx with ⟨headTrace⟩
      rcases ih htail with ⟨tailTrace⟩
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
      .ok (state, out)) :
    Nonempty (SystemMessageTrace benv target data state out) := by
  have hmessage : processMessageCall
      (systemTransactionMessage benv target data) = .ok (state, out) := by
    simpa [processUncheckedSystemTransaction, processSystemTransaction,
      systemTransactionMessage] using h
  rcases exists_messageCallTrace hmessage with ⟨trace⟩
  exact ⟨⟨trace, h⟩⟩

/-- Retained execution evidence for the two checked request-system calls at
the tail of `applyBody`. -/
structure RequestsTrace (benv : Benv) (bout : BlockOutput)
    (state : State) (bout' : BlockOutput) where
  depositRequests : Bytes
  parsed : parseDepositRequests bout = .ok depositRequests
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
    (h : processGeneralPurposeRequests benv bout = .ok (state, bout')) :
    Nonempty (RequestsTrace benv bout state bout') := by
  have h_result := h
  unfold processGeneralPurposeRequests at h
  obtain ⟨deposits, hdeposits, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h <;>
    (obtain ⟨⟨withdrawalState, withdrawalOut⟩, hwithdrawal, h⟩ :=
      Except.bind_eq_ok h
     have hwithdrawal' :=
       processCheckedSystemTransaction_to_unchecked hwithdrawal
     rcases exists_systemMessageTrace hwithdrawal' with ⟨withdrawalTrace⟩
     dsimp only at h
     split at h <;>
       (obtain ⟨⟨consolidationState, consolidationOut⟩,
          hconsolidation, _⟩ := Except.bind_eq_ok h
        have hconsolidation' :=
          processCheckedSystemTransaction_to_unchecked hconsolidation
        rcases exists_systemMessageTrace hconsolidation' with
          ⟨consolidationTrace⟩
        exact ⟨⟨deposits, hdeposits,
          withdrawalState, withdrawalOut, hwithdrawal, withdrawalTrace,
          consolidationState, consolidationOut,
          hconsolidation, consolidationTrace, h_result⟩⟩))

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
  requests : RequestsTrace
    (transactionBenv.withState
      (processWithdrawalsState transactionBenv.state wds))
    (transactionBout.withWithdrawalsTrie
      (processWithdrawalsTrie transactionBout.withdrawalsTrie wds))
    state bout
theorem exists_appliedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (h : applyBody benv txs wds = .ok (state, bout)) :
    Nonempty (AppliedBodyTrace benv txs wds state bout) := by
  have h_result := h
  rw [applyBody] at h
  simp only at h
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
  rcases exists_systemMessageTrace hbeacon with ⟨beaconTrace⟩
  rcases exists_systemMessageTrace hhistory with ⟨historyTrace⟩
  rcases exists_applyTransactionsTrace htransactions with
    ⟨transactionsTrace⟩
  dsimp [processWithdrawals] at hrequests
  rcases exists_requestsTrace hrequests with ⟨requestsTrace⟩
  exact ⟨⟨h_result, beaconState, beaconOut, beaconTrace,
    lastHash, hlastHash, historyState, historyOut, historyTrace,
    decodedTxs, hdecoded, transactionBenv, transactionBout,
    transactionsTrace, requestsTrace⟩⟩

end ExecutionTrace

end Blanc
