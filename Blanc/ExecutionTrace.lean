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
  /-- **The Amsterdam top-level path.**

  Under `rules.stateGas = some sgr` both wrapper arms route through
  `processTopLevelAmsterdam`, which prepares, runs and settles the frame in one
  step rather than through the create/call shapes the other three constructors
  name. The trace records which lane ran and the result it produced; it
  deliberately claims nothing about the internal shape, because Blanc has no
  vocabulary for the metered lifecycle yet.

  `h_rules` is what makes this case free at every consumer: a contract theorem
  fixes a concrete `Fork`, and `Fork.ruleSet` of any fork but Amsterdam has
  `stateGas = none`, so the case closes by computation. -/
  | topLevelAmsterdam
      (sgr : StateGasRules)
      (h_rules : msg.benv.stat.rules.stateGas = some sgr)
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
    rcases hsg : msg.benv.stat.rules.stateGas with _ | sgr
    case some => exact ⟨.topLevelAmsterdam sgr hsg h_result⟩
    simp only [hsg] at h
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
    rcases hsg : msg.benv.stat.rules.stateGas with _ | sgr
    case some => exact ⟨.topLevelAmsterdam sgr hsg h_result⟩
    simp only [hsg] at h
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

open private recoverValidationSender from Jaune.Transaction in
/-- Exact local name for the recovery operation used by the pinned driver. -/
def transactionValidationRecovery (benv : Benv) (tx : Tx) :
    Except TransitionError Adr :=
  recoverValidationSender benv tx

/-- Validation bounds the actual charged amount for either settlement rule. -/
theorem settleTransactionGas_gasUsed_le (rules : ForkRules)
    (gas floor left stateLeft refund : Nat) (net : Int) (floorLe : floor ≤ gas) :
    (settleTransactionGas rules gas floor left stateLeft refund net).gasUsed ≤ gas := by
  cases h : rules.stateGas <;> simp only [settleTransactionGas, h] <;>
    exact max_le (by omega) floorLe

/-- The sender's refundable gas is the complement of the actual charged gas. -/
theorem settleTransactionGas_gasLeft_eq (rules : ForkRules)
    (gas floor left stateLeft refund : Nat) (net : Int) :
    (settleTransactionGas rules gas floor left stateLeft refund net).gasLeft =
      gas - (settleTransactionGas rules gas floor left stateLeft refund net).gasUsed := by
  cases h : rules.stateGas <;> simp only [settleTransactionGas, h]

/-- Both actual settlement credits are funded by the upfront gas payment. -/
theorem settleTransactionGas_credits_le (rules : ForkRules)
    (gas floor left stateLeft refund price base : Nat) (net : Int)
    (floorLe : floor ≤ gas) :
    let settlement := settleTransactionGas rules gas floor left stateLeft refund net
    settlement.gasLeft * price + settlement.gasUsed * (price - base) ≤ gas * price := by
  dsimp only
  rw [settleTransactionGas_gasLeft_eq]
  apply le_trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.sub_le price base)) _)
  rw [← Nat.add_mul, Nat.sub_add_cancel
    (settleTransactionGas_gasUsed_le rules gas floor left stateLeft refund net floorLe)]

/-- The single account operation selected by the transaction's deletion rule. -/
def settleSelfdestructsStep (rules : ForkRules) (state : State) (address : Adr) : State :=
  match rules.stateGas with
  | none => destroyAccount state address
  | some _ => clearAccountPreservingBalance state address

/-- The driver applies the selected account operation in the retained list order. -/
theorem settleSelfdestructs_eq_foldl (rules : ForkRules)
    (addresses : List Adr) (state : State) :
    settleSelfdestructs rules addresses state =
      addresses.foldl (settleSelfdestructsStep rules) state := by
  unfold settleSelfdestructsStep
  cases h : rules.stateGas <;> simp only [settleSelfdestructs, h]

/-- Clearing account data preserves the entire balance function, including the target. -/
theorem clearAccountPreservingBalance_bal (state : State) (address : Adr) :
    (clearAccountPreservingBalance state address).bal = state.bal := by
  funext ca
  unfold State.bal clearAccountPreservingBalance
  by_cases h : address = ca
  · subst ca
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

/-- A selected deletion step leaves every unlisted account completely unchanged. -/
theorem settleSelfdestructsStep_get_eq (rules : ForkRules)
    {ca address : Adr} {state : State} (hne : address ≠ ca) :
    (settleSelfdestructsStep rules state address).get ca = state.get ca := by
  cases h : rules.stateGas
  · simp only [settleSelfdestructsStep, h]
    unfold destroyAccount State.get
    have hc : compare address ca ≠ Ordering.eq :=
      fun eq => hne (compare_eq_iff_eq.mp eq)
    rw [Std.TreeMap.getD_erase]
    simp [hc]
  · simp only [settleSelfdestructsStep, h]
    exact State.get_set_ne _ hne _

/-- The complete rules-selected deletion fold preserves every unlisted account. -/
theorem settleSelfdestructs_get_eq (rules : ForkRules)
    {ca : Adr} {state : State} {addresses : List Adr}
    (hne : ∀ address ∈ addresses, address ≠ ca) :
    (settleSelfdestructs rules addresses state).get ca = state.get ca := by
  rw [settleSelfdestructs_eq_foldl]
  induction addresses generalizing state with
  | nil => rfl
  | cons address addresses ih =>
      rw [List.foldl_cons, ih]
      · exact settleSelfdestructsStep_get_eq rules (hne address List.mem_cons_self)
      · intro tail htail
        exact hne tail (List.mem_cons_of_mem _ htail)

open private recoverValidationSender from Jaune.Transaction in
theorem transactionValidationRecovery_legacy
    (benv : Benv) (tx : Tx) (hlegacy : benv.stat.rules.stateGas = none) :
    transactionValidationRecovery benv tx = .ok 0 := by
  simp only [transactionValidationRecovery, recoverValidationSender, hlegacy]

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
        gas := (allocateEvmGas benv.stat.rules tx.gas intrinsicGas).executionGas
        stateGasReservoir := (allocateEvmGas benv.stat.rules tx.gas intrinsicGas).stateGasReservoir
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
  validationSender : Adr
  recovered : transactionValidationRecovery benv.beginTransaction tx = .ok validationSender
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
    (h : processTransaction benv bout tx index = .ok (state, bout')) :
    Nonempty (TransactionTrace benv bout tx index state bout') := by
  have h_result := h
  unfold processTransaction at h
  dsimp only at h
  obtain ⟨prelude, hprelude, h⟩ := Except.bind_eq_ok h
  cases hprelude
  obtain ⟨validationSender, hrecovered, h⟩ := Except.bind_eq_ok h
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
    msg, messageState, messageOut, validationSender,
    by simpa only [transactionValidationRecovery] using hrecovered,
    by simpa [Benv.beginTransaction, BenvStat.rules] using hvalidated,
    by simpa [transactionPreludeBout] using hchecked,
    by simpa [transactionBlobGasFee, Benv.beginTransaction, BenvStat.rules] using hdebit',
    by simpa [transactionTenv, Benv.beginTransaction] using hprepared,
    messageTrace, h_result⟩⟩

/-- Exact post-message transaction settlement form.  This exposes the two
gas credits and the final account-deletion fold without re-executing or
approximating the transaction. -/
theorem TransactionTrace.exists_finalStateFormWithRules
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    ∃ refundCounter : Nat,
      Int.toNat? trace.messageOut.refundCounter = some refundCounter ∧
      state =
        settleSelfdestructs benv.beginTransaction.stat.rules
          trace.messageOut.accountsToDelete.toList
          ((trace.messageState.addBal trace.sender
              ((settleTransactionGas benv.beginTransaction.stat.rules tx.gas
                trace.calldataFloorGasCost trace.messageOut.gasLeft
                trace.messageOut.stateGasLeft refundCounter
                trace.messageOut.stateGasUsed).gasLeft * trace.effectiveGasPrice).toB256).addBal
            benv.beginTransaction.stat.coinbase
              ((settleTransactionGas benv.beginTransaction.stat.rules tx.gas
                trace.calldataFloorGasCost trace.messageOut.gasLeft
                trace.messageOut.stateGasLeft refundCounter
                trace.messageOut.stateGasUsed).gasUsed *
                (trace.effectiveGasPrice - benv.beginTransaction.stat.baseFeePerGas)).toB256) := by
  have hrun := trace.result
  unfold processTransaction at hrun
  dsimp only at hrun
  rcases Except.bind_eq_ok hrun with ⟨prelude, hprelude, hrun⟩
  have hpreludeEq := Except.ok.inj hprelude
  subst prelude
  rcases Except.bind_eq_ok hrun with ⟨validationSender, hrecovered, hrun⟩
  have hsender : validationSender = trace.validationSender := by
    exact Except.ok.inj (hrecovered.symm.trans trace.recovered)
  rcases Except.bind_eq_ok hrun with ⟨validated, hvalidated, hrun⟩
  rcases validated with ⟨intrinsicGas, calldataFloorGasCost⟩
  rw [Except.mapError_eq_ok_iff] at hvalidated
  rw [hsender] at hvalidated
  have hvalidated : validateTransaction benv.stat.rules tx
      (trace.validationSender) = .ok (intrinsicGas, calldataFloorGasCost) := by
    simpa only [Benv.beginTransaction, BenvStat.rules] using hvalidated
  have hvalidatedEq : intrinsicGas = trace.intrinsicGas ∧
      calldataFloorGasCost = trace.calldataFloorGasCost := by
    exact Prod.mk.inj (Except.ok.inj (hvalidated.symm.trans trace.validation))
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
    have htraceDebit := trace.debit
    simp only [transactionBlobGasFee, Benv.beginTransaction, BenvStat.rules] at htraceDebit hdebitSome
    rw [htraceDebit] at hdebitSome
    exact Option.some.inj hdebitSome.symm
  subst debitState
  rcases Except.bind_eq_ok hrun with ⟨msg, hprepared, hrun⟩
  have hmsgEq : msg = trace.msg := Except.ok.inj
    (hprepared.symm.trans trace.prepared)
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
  simp only at hrun
  have hfinal := Except.ok.inj hrun
  exact ⟨refundCounter, hrefundSome, (Prod.mk.inj hfinal).1.symm⟩

/-- Legacy specialization of the exact rules-selected final state. -/
theorem TransactionTrace.exists_finalStateForm_legacy
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hlegacy : benv.stat.rules.stateGas = none) :
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
  have hlegacy' : (Fork.ruleSet benv.stat.fork).stateGas = none := hlegacy
  simpa only [settleSelfdestructs, settleTransactionGas, Benv.beginTransaction,
    BenvStat.rules, hlegacy'] using trace.exists_finalStateFormWithRules

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
  /-- **The two request contracts this trace is about are the ones the rules
  name, in order.**

  Jaune's request pass is now a fold over `rules.requests` -- an ordered list of
  `(type byte, address)` pairs -- rather than two named calls, and Amsterdam
  appends two more entries. Pinning the list is what keeps this structure's two
  named calls faithful: under Prague, Osaka, BPO1 and BPO2 the list is exactly
  these two, so the fields below are the fold, spelled out. Under a fork that
  names a different list the structure is uninhabited, which is honest -- Blanc
  has no theory of the extra contracts yet.

  Every consumer fixes a concrete `Fork`, so this is discharged by
  computation. -/
  requestsShape : benv.stat.rules.requests =
    [(1, withdrawalRequestPredeployAddress),
     (2, consolidationRequestPredeployAddress)]
  run : processGeneralPurposeRequests benv bout = .ok (state, bout')

theorem exists_requestsTrace
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (hreq : benv.stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)])
    (h : processGeneralPurposeRequests benv bout = .ok (state, bout')) :
    Nonempty (RequestsTrace benv bout state bout') := by
  have h_result := h
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at h
  rw [hreq] at h
  unfold runRequestContracts at h
  obtain ⟨deposits, hdeposits, h⟩ := Except.bind_eq_ok h
  -- The fold now returns a triple -- state, the accumulated request bytes, and
  -- EIP-7928's builder -- so peel the fold itself before its steps.
  obtain ⟨⟨foldState, foldRequests, foldBal⟩, hfold, _⟩ := Except.bind_eq_ok h
  -- The fold's first step: the withdrawal contract.
  obtain ⟨⟨withdrawalState, withdrawalOut⟩, hwithdrawal, hfold⟩ :=
    Except.bind_eq_ok hfold
  have hwithdrawal' :=
    processCheckedSystemTransaction_to_unchecked hwithdrawal
  rcases exists_systemMessageTrace hwithdrawal' with ⟨withdrawalTrace⟩
  -- and its second: the consolidation contract, on the threaded environment.
  unfold runRequestContracts at hfold
  obtain ⟨⟨consolidationState, consolidationOut⟩, hconsolidation, _⟩ :=
    Except.bind_eq_ok hfold
  have hconsolidation' :=
    processCheckedSystemTransaction_to_unchecked hconsolidation
  rcases exists_systemMessageTrace hconsolidation' with ⟨consolidationTrace⟩
  exact ⟨⟨deposits, hdeposits,
    withdrawalState, withdrawalOut, hwithdrawal, withdrawalTrace,
    consolidationState, consolidationOut,
    hconsolidation, consolidationTrace, hreq, h_result⟩⟩

/-- The final request-processing state is the state returned by the second
checked system message. -/
theorem RequestsTrace.state_eq_consolidationState
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    state = trace.consolidationState := by
  -- The fold threads the environment as `benv.withState _`, so the field is
  -- used in the form it is stated in rather than simped into a record literal.
  have hrun := trace.run
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at hrun
  rw [trace.requestsShape] at hrun
  unfold runRequestContracts at hrun
  rw [trace.parsed] at hrun
  simp only [bind, Except.bind] at hrun
  rw [trace.withdrawalRun] at hrun
  simp only [bind, Except.bind] at hrun
  unfold runRequestContracts at hrun
  rw [trace.consolidationRun] at hrun
  simp only [bind, Except.bind] at hrun
  exact (Prod.mk.inj (Except.ok.inj hrun)).1.symm

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
  /-- The block output the transaction fold starts from. Under EIP-7928 this is
  `BlockOutput.init` seeded with the builder the two pre-execution system calls
  incorporated at index 0; under `bal = none` the builder is inert. Named rather
  than spelled out because Blanc has no `BalBuilder` vocabulary and this trace
  claims nothing about one. -/
  initialBout : BlockOutput
  transactionBenv : Benv
  transactionBout : BlockOutput
  transactions : ApplyTransactionsTrace decodedTxs.putIndex
    ((benv.withState beaconState).withState historyState) initialBout
    transactionBenv transactionBout
  /-- The block output handed to the request pass: the withdrawals-trie update,
  plus the withdrawals batch's own EIP-7928 incorporation. Named for the same
  reason as `initialBout`. -/
  requestsBoutIn : BlockOutput
  /-- `applyBody` no longer ends at the request pass: it builds the block access
  list, checks the item rule against the block gas limit, and returns
  `{boutReq with blockAccessList := list}`. So the request pass's own outputs
  are one step before the body's, and the trace names both. `run` below still
  pins the whole run, and the built list is left unconstrained -- it is
  observation metadata Blanc has no theory of (DP-E3d). -/
  requestsState : State
  requestsBout : BlockOutput
  requests : RequestsTrace
    (transactionBenv.withState
      (processWithdrawalsState transactionBenv.state wds))
    requestsBoutIn requestsState requestsBout
/-- **The transaction fold carries the block's static environment.**

`applyTransactions` only ever rebuilds its environment with `Benv.withState`,
which rewrites `state` and copies `stat` through, so the fork -- and with it the
request-contract list -- is the block's throughout. -/
theorem applyTransactions_stat :
    ∀ (txis : List (Nat × Tx)) {benv : Benv} {bout : BlockOutput}
      {p : Benv × BlockOutput},
      applyTransactions txis benv bout = .ok p → p.1.stat = benv.stat
  | [], _, _, _, hp => by cases hp; rfl
  | txi :: txis, benv, bout, p, hp => by
    unfold applyTransactions at hp
    obtain ⟨⟨st, bout'⟩, _, hp⟩ := Except.bind_eq_ok hp
    dsimp only at hp
    -- The recursive call runs on `benv.withState st`. Its `stat` is `benv`'s by
    -- definition, so the induction hypothesis *is* the goal -- but the implicit
    -- has to be given, or it unifies against the goal's `benv` and `hp` no
    -- longer matches.
    have ih := applyTransactions_stat (benv := benv.withState st) txis hp
    exact ih

theorem exists_appliedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (hreq : benv.stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)])
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
  -- `applyBody`'s tail: the request pass, then the access-list build and its
  -- gas-limit check.
  rcases Except.bind_eq_ok hrequests with
    ⟨⟨requestsState, requestsBout⟩, hrequests, _⟩
  have hreq' : (transactionBenv.withState
      (processWithdrawalsState transactionBenv.state wds)).stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := by
    show transactionBenv.stat.rules.requests = _
    rw [applyTransactions_stat _ htransactions]
    exact hreq
  rcases exists_requestsTrace hreq' hrequests with ⟨requestsTrace⟩
  exact ⟨⟨h_result, beaconState, beaconOut, beaconTrace,
    lastHash, hlastHash, historyState, historyOut, historyTrace,
    decodedTxs, hdecoded, _, transactionBenv, transactionBout,
    transactionsTrace, _, requestsState, requestsBout, requestsTrace⟩⟩

end ExecutionTrace

end Blanc
