import Blanc.ExecutionAccountingReplay
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionTraceSettledFrames

/-!
# Observed semantic accounting under trace-local admission

A committed execution root supplies a replay whose observation is exactly its
committed frames. The wrapper ladder threads admission along actual retained
runs and composes those replays in settlement order. Reverted frames and failed
CREATE settlements contribute no observations through the existing settlement
engines, including ancestor rollback.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A retained transaction's prepared message inherits the transaction's
opening word bound: only the nonce bump and the fee debit precede it. -/
theorem TransactionTrace.msg_sum_nof
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (sumNof : sum benv.state.bal < 2 ^ 256) :
    sum trace.msg.benv.state.bal < 2 ^ 256 := by
  have debitSum := State.balSum_subBal trace.debit
  dsimp only [State.balSum] at debitSum
  rw [State.incrNonce_bal] at debitSum
  rw [prepareMessage_benv trace.prepared]
  change sum trace.debitState.bal < 2 ^ 256
  omega

/-- The direct consensus withdrawals keep the world total below the word bound
whenever the block bound holds. -/
theorem processWithdrawalsState_sum_nof {pre : State} {wds : List Withdrawal}
    (bound : sum pre.bal + wdsum wds < 2 ^ 256) :
    sum (processWithdrawalsState pre wds).bal < 2 ^ 256 := by
  induction wds generalizing pre with
  | nil =>
      rw [processWithdrawalsState_nil]
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bound
  | cons wd wds ih =>
      rw [processWithdrawalsState_cons]
      exact ih (withdrawalCredit_bounds bound).2

/-- G+1.  A transaction's prepared message is sent by its checked sender. -/
theorem TransactionTrace.msg_caller
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.msg.caller = trace.sender := by
  have prepared := trace.prepared
  unfold prepareMessage at prepared
  injection prepared with h
  rw [← h]
  rfl

/-- G+3.  The direct withdrawals move balances only. -/
theorem processWithdrawalsState_getStor_eq (ca : Adr) (state : State)
    (withdrawals : List Withdrawal) :
    (processWithdrawalsState state withdrawals).getStor ca = state.getStor ca := by
  induction withdrawals generalizing state with
  | nil => rfl
  | cons withdrawal withdrawals ih =>
      rw [processWithdrawalsState_cons, ih]
      show ((state.setBal withdrawal.recipient _).get ca).stor = (state.get ca).stor
      rw [State.setBal_get_stor]

/-- G+4.  The block's withdrawal bound survives the body prefix. -/
theorem AppliedBodyTrace.transactionBound
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
  have beacon := processMessageCall_sum_le
    (by simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hfork.rules_stateGas_none)
    trace.beacon.message.result
  have history := processMessageCall_sum_le
    (by simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction, Benv.withState] using hfork.rules_stateGas_none)
    trace.history.message.result
  have transactions := trace.transactions.sum_le (by
    simpa only [Benv.withState] using hfork)
  simp only [systemTransactionMessage_benv_state, Benv.withState] at beacon history transactions
  omega

end ExecutionTrace

namespace ExecutionAccountingReplay

/-! ## Direct balance credits -/

namespace ReplayCarrier

variable {ca : Adr}

/-- `ofAddBal`, observed: the credit it may produce is observed as nothing. -/
theorem ofAddBal_observed (C : ReplayCarrier ca) (V : ReplayObservation C)
    (tag : C.Tag)
    {target : Adr} {pre : State} {value : B256}
    (sum_nof : sum pre.bal + value.toNat < 2 ^ 256) :
    ∃ steps, C.Replay (C.ofState pre) steps
      (C.ofState (pre.addBal target value)) ∧ V.obs steps = [] := by
  have storage_eq :
      (pre.addBal target value).getStor ca = pre.getStor ca := by
    show ((pre.setBal target (pre.bal target + value)).get ca).stor =
      (pre.get ca).stor
    rw [State.setBal_get_stor]
  apply C.ofStorageEqBalanceMono_observed V tag storage_eq
  by_cases target_eq : target = ca
  · subst target
    have nof : B256.Nof (pre.bal ca) value := by
      unfold B256.Nof
      have target_le : (pre.bal ca).toNat ≤ sum pre.bal := le_sum
      omega
    have word_eq : (pre.addBal ca value).bal ca = pre.bal ca + value := by
      show ((pre.setBal ca (pre.bal ca + value)).get ca).bal = _
      rw [State.setBal_get_self]
      rfl
    rw [word_eq, B256.toNat_add_eq_of_nof _ _ nof]
    omega
  · have balance_eq : (pre.addBal target value).bal ca = pre.bal ca := by
      show ((pre.setBal target (pre.bal target + value)).get ca).bal = _
      rw [State.setBal_get_ne target_eq]
      rfl
    exact le_of_eq (congrArg B256.toNat balance_eq.symm)


end ReplayCarrier

/-- An observed account-local replay ladder under admission at concrete frame roots.
The semantic contract may describe deployed bytecode without a source `Prog`.
Only `root` interprets an execution; all higher rungs reuse settlement and the
retained wrapper chronology. -/
structure AccountingLadderAdmitted (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) where
  carrier : ReplayCarrier ca
  append : ∀ {pre mid post : carrier.Snap} {left right : List carrier.Step},
    carrier.Replay pre left mid → carrier.Replay mid right post →
      carrier.Replay pre (left ++ right) post
  tag : Nat → Option Nat → carrier.Tag
  preserves : c.PreservesAdmitted ca entry
  view : ReplayObservation carrier
  root : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entryBenv : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out),
    msg.benvAfterTransfer = .ok entryBenv →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entryBenv) →
    ∀ committed : Execution.commits out = true,
    Exec.FrameAdmitted ca entry run →
    c.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    CoveredFork sevm.benvStat.fork →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∃ steps, carrier.Replay (carrier.frameEntry sevm pre.state) steps
      (carrier.ofState (Execution.committedPost out committed).state) ∧
      view.obs steps = (Exec.committedFrames run).flatMap view.frameObs

open _root_.Blanc.ExecutionTrace in
/-- A colliding CREATE wrapper runs no frame. -/
theorem _root_.Blanc.ExecutionTrace.MessageCallTrace.settledFrames_eq_nil_of_collision
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (receiver : msg.target.isNone = true)
    (collision : messageCreateCollision msg = true) :
    trace.settledFrames = [] := by
  cases trace with
  | createCollision => rfl
  | createRun _ noCollision => simp_all only [Bool.false_eq_true]
  | callRun noTarget => simp_all only [Bool.false_eq_true]


namespace AccountingLadderAdmitted

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

private theorem ite_flatMap {α β : Type} (c : Prop) [Decidable c]
    (l : List α) (f : α → List β) :
    (if c then l else []).flatMap f = if c then l.flatMap f else [] := by
  split <;> simp only [List.flatMap_nil]

/-- G1, observed. -/
theorem processMessage (L : AccountingLadderAdmitted c ca entry)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed L.view
          (L.tag blockIndex transactionIndex)
          (congrFun
            (_root_.Blanc.ExecutionTrace.ProcessMessage.none_ok_getStor_eq
              process) ca)
          (_root_.Blanc.ProcessMessage.targetBalanceMono_of_none process
            runReady.ready.ne sumNof)
      exact ⟨steps, replay, by simp only [observed,
        ExecutionTrace.ProcessMessageTrace.settledFrames, List.flatMap_nil]⟩
  | @some pc sevm pre out run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      simp only [Frame.ofCall] at transfer evmEq
      have rootFork : CoveredFork sevm.benvStat.fork := by
        have sevmEq : sevm = initSevm (msg.withBenv entry) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact hfork
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.toSettlementCarrier.processMessage_of_body_observed
          L.view.obs L.view.obs_nil process runReady.ready.ne
          runReady.ready.val0 sumNof fun committed =>
            L.root blockIndex transactionIndex run transfer evmEq committed admitted
              runReady callerNe rootFork sumNof
      refine ⟨steps, replay, ?_⟩
      rw [observed]
      simp only [ExecutionTrace.ProcessMessageTrace.settledFrames, ite_flatMap]

/-- G2, observed. -/
theorem processCreateMessage (L : AccountingLadderAdmitted c ca entry)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed L.view
          (L.tag blockIndex transactionIndex)
          (congrFun
            (_root_.Blanc.ExecutionTrace.ProcessCreateMessage.none_ok_getStor_eq_of_empty
              process fresh) ca)
          (_root_.Blanc.ProcessCreateMessage.targetBalanceMono_of_none process
            runReady.ready.ne sumNof)
      exact ⟨steps, replay, by simp only [observed,
        ExecutionTrace.ProcessCreateMessageTrace.settledFrames, List.flatMap_nil]⟩
  | @some pc sevm pre out run =>
      have preparedInv :=
        runReady.ready.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe :
          (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by
          simpa only [processCreateMessage.msg, Msg.withBenv] using target)
      have preparedSum :
          sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [_root_.Jaune.processCreateMessage_msg_bal_eq]
        exact sumNof
      have preparedFork :
          CoveredFork (processCreateMessage.msg msg).benv.stat.fork := by
        rw [processCreateMessage.msg_benvStat]
        exact hfork
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      simp only [Frame.ofCreate] at transfer evmEq
      have rootFork : CoveredFork sevm.benvStat.fork := by
        have sevmEq :
            sevm = initSevm ((processCreateMessage.msg msg).withBenv entry) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact preparedFork
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.toSettlementCarrier.processCreateMessage_of_body_observed
          L.view.obs L.view.obs_nil process runReady.ready.ne
          runReady.ready.val0 fresh sumNof fun committed =>
            L.root blockIndex transactionIndex run transfer evmEq committed admitted
              (preparedInv.runReady_of_foreign preparedTargetNe)
              (fun target => absurd target preparedTargetNe) rootFork preparedSum
      refine ⟨steps, replay, ?_⟩
      rw [observed]
      simp only [ExecutionTrace.ProcessCreateMessageTrace.settledFrames,
        ite_flatMap]

open _root_.Blanc.ExecutionTrace in
/-- G3, observed. -/
theorem messageCall (L : AccountingLadderAdmitted c ca entry)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  cases trace with
  | createCollision targetNone collision result =>
      have stateEq :=
        processMessageCall_createCollision_state_eq targetNone collision result hfork
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed L.view
          (L.tag blockIndex transactionIndex)
          (pre := msg.benv.state) (post := state)
          (by rw [stateEq]) (by rw [stateEq])
      exact ⟨steps, replay, by simp only [observed, MessageCallTrace.settledFrames,
        List.flatMap_nil]⟩
  | createRun targetNone collision evm core inner result =>
      have targetNe : msg.currentTarget ≠ ca := by
        rcases runReady.codeOrForeign with call | foreign
        · exact Bool.noConfusion (targetNone.symm.trans call)
        · exact foreign
      have fresh := messageCreateCollision_false_getStor_eq_empty collision
      obtain ⟨steps, replay, observed⟩ :=
        L.processCreateMessage inner admitted runReady hfork sumNof targetNone targetNe
          fresh blockIndex transactionIndex
      refine ⟨steps, ?_, by simpa only [MessageCallTrace.settledFrames,
        ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq] using observed⟩
      rw [processMessageCall_createRun_state_eq targetNone collision core result hfork]
      exact replay
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm
      core inner result =>
      subst execMsgEq
      have stateEq :=
        processMessageCall_callRun_state_eq targetSome delegation rfl core
          result hfork
      have delegatedInv := runReady.ready.of_messageCallDelegation delegation
      have execReady :
          c.MessageRunReady ca (messageCallExecutionMessage delegated) := by
        refine ⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩
        rw [messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact targetSome
      have execCallerNe :
          (messageCallExecutionMessage delegated).currentTarget = ca →
            (messageCallExecutionMessage delegated).caller ≠ ca := by
        intro target
        rw [messageCallExecutionMessage_currentTarget_eq,
          messageCallDelegation_currentTarget_eq delegation] at target
        rw [messageCallExecutionMessage_caller_eq,
          messageCallDelegation_caller_eq delegation]
        exact callerNe target
      have storEq :
          (messageCallExecutionMessage delegated).benv.state.getStor =
            msg.benv.state.getStor := by
        rw [messageCallExecutionMessage_getStor_eq,
          messageCallDelegation_getStor_eq delegation]
      have balEq :
          (messageCallExecutionMessage delegated).benv.state.bal =
            msg.benv.state.bal := by
        rw [messageCallExecutionMessage_bal_eq,
          messageCallDelegation_bal_eq delegation]
      have snapshotEq :
          L.carrier.ofState (messageCallExecutionMessage delegated).benv.state =
            L.carrier.ofState msg.benv.state :=
        L.carrier.silent (congrFun storEq ca)
          (congrArg B256.toNat (congrFun balEq ca))
      have execSum :
          sum (messageCallExecutionMessage delegated).benv.state.bal <
            2 ^ 256 := by
        rw [balEq]
        exact sumNof
      have execFork :
          CoveredFork (messageCallExecutionMessage delegated).benv.stat.fork := by
        rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hfork
      obtain ⟨steps, replay, observed⟩ :=
        L.processMessage inner admitted execReady execCallerNe execFork execSum
          blockIndex transactionIndex
      refine ⟨steps, ?_, by simpa only [MessageCallTrace.settledFrames,
        ProcessMessageTrace.settledFrames, ExceptT.stM_eq] using observed⟩
      rw [stateEq, ← snapshotEq]
      exact replay

open _root_.Blanc.ExecutionTrace in
/-- G3', observed. -/
theorem transactionMessage (L : AccountingLadderAdmitted c ca entry)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (msgInv : c.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  have transfer : trace.msg.shouldTransferValue = true :=
    trace.msg_shouldTransferValue
  have msgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hfork
  simp only [TransactionTrace.settledFrames]
  by_cases target : trace.msg.currentTarget = ca
  · cases receiver : trace.msg.target.isNone with
    | false =>
        exact L.messageCall trace.message admitted (msgInv.runReady_of_call receiver)
          (fun _ => msgInv.ne transfer) msgFork sumNof blockIndex transactionIndex
    | true =>
        have collision : messageCreateCollision trace.msg = true := by
          cases test : messageCreateCollision trace.msg with
          | false =>
              exact absurd target
                (ContractSpecSem.StateInv.ne_of_messageCreateCollision_false
                  msgInv.state test)
          | true => rfl
        have stateEq : trace.messageState = trace.msg.benv.state :=
          processMessageCall_createCollision_state_eq receiver collision
            trace.message.result msgFork
        refine ⟨[], L.carrier.nilOfEq (congrArg L.carrier.ofState stateEq), ?_⟩
        rw [trace.message.settledFrames_eq_nil_of_collision receiver collision]
        simpa only [List.flatMap_nil] using L.view.obs_nil
  · exact L.messageCall trace.message admitted (msgInv.runReady_of_foreign target)
      (fun current => absurd current target) msgFork sumNof blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in
/-- G4, observed: the two gas credits are observed as nothing. -/
theorem transaction (L : AccountingLadderAdmitted c ca entry)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  rcases trace.exists_stateChronology hfork with ⟨chronology⟩
  have senderNe : trace.sender ≠ ca := trace.sender_ne_sem inv notCreated
  -- (1) nonce bump and fee debit: invisible at `ca`
  have debitSnapshot :
      L.carrier.ofState trace.msg.benv.state =
        L.carrier.ofState benv.state := by
    rw [prepareMessage_benv trace.prepared]
    show L.carrier.ofState trace.debitState = _
    exact L.carrier.silent trace.debitState_getStor_eq
      (congrArg B256.toNat (trace.debitState_bal_eq senderNe))
  -- (2) the prepared message, by G3'
  obtain ⟨messageSteps, messageReplay, messageObserved⟩ :=
    L.transactionMessage trace admitted (trace.msgInv_sem inv notCreated)
      (trace.msg_sum_nof sumNof) hfork blockIndex transactionIndex
  rw [debitSnapshot] at messageReplay
  -- (3), (4) the two gas credits, funded by the transaction's own debit
  obtain ⟨refundBound, tipBound⟩ :=
    trace.settlement_sum_bounds chronology.refundCounter sumNof hfork
  obtain ⟨refundSteps, refundReplay, refundObserved⟩ :=
    L.carrier.ofAddBal_observed L.view (L.tag blockIndex transactionIndex)
      (target := trace.sender) (pre := trace.messageState)
      (value := trace.refundValue chronology.refundCounter) refundBound
  obtain ⟨tipSteps, tipReplay, tipObserved⟩ :=
    L.carrier.ofAddBal_observed L.view (L.tag blockIndex transactionIndex)
      (target := benv.stat.coinbase)
      (pre := trace.refundedState chronology.refundCounter)
      (value := trace.coinbaseValue chronology.refundCounter) tipBound
  have refundReplay' :
      L.carrier.Replay (L.carrier.ofState trace.messageState) refundSteps
        (L.carrier.ofState (trace.refundedState chronology.refundCounter)) :=
    refundReplay
  -- (5) the deletion fold never names `ca`
  have deleteGet := foldl_destroyAccount_get_eq
    (state := trace.coinbaseState chronology.refundCounter)
    (trace.message.stateInv_admitted_sem L.preserves (by
      rw [prepareMessage_benv trace.prepared]
      simpa only [Benv.beginTransaction] using hfork) admitted
      (trace.msgInv_sem inv notCreated)).2
  have finalSnapshot :
      L.carrier.ofState state =
        L.carrier.ofState (trace.coinbaseState chronology.refundCounter) :=
    (congrArg L.carrier.ofState chronology.finalState_eq).trans
      (L.carrier.silent (congrArg Acct.stor deleteGet)
        (congrArg B256.toNat (congrArg Acct.bal deleteGet)))
  have tipReplay' :
      L.carrier.Replay
        (L.carrier.ofState (trace.refundedState chronology.refundCounter))
        tipSteps (L.carrier.ofState state) := by
    rw [finalSnapshot]
    exact tipReplay
  refine ⟨messageSteps ++ (refundSteps ++ tipSteps),
    L.append messageReplay (L.append refundReplay' tipReplay'), ?_⟩
  rw [L.view.obs_append, L.view.obs_append, messageObserved, refundObserved,
    tipObserved]
  simp only [TransactionTrace.settledFrames, MessageCallTrace.settledFrames,
    ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq, ProcessMessageTrace.settledFrames,
    List.append_nil]

open _root_.Blanc.ExecutionTrace in
/-- G5, observed. -/
theorem transactionList (L : AccountingLadderAdmitted c ca entry)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  induction trace with
  | nil =>
      exact ⟨[], L.carrier.nilOfEq rfl, by simpa only [ApplyTransactionsTrace.settledFrames,
        List.flatMap_nil] using L.view.obs_nil⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail
      ih =>
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        L.transaction head admitted.1 inv notCreated sumNof hfork blockIndex (some index)
      have next : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_sem L.preserves hfork admitted.1 sumNof ⟨inv, notCreated⟩
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hfork.rules_stateGas_none)
          sumNof
      obtain ⟨tailSteps, tailReplay, tailObserved⟩ :=
        ih admitted.2 next.state next.ca nextSum (by simpa only [Benv.withState] using hfork)
      refine ⟨headSteps ++ tailSteps, L.append headReplay tailReplay, ?_⟩
      rw [L.view.obs_append, headObserved, tailObserved]
      simp only [TransactionTrace.settledFrames, MessageCallTrace.settledFrames,
        ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq, ProcessMessageTrace.settledFrames,
        ApplyTransactionsTrace.settledFrames, List.flatMap_append]

open _root_.Blanc.ExecutionTrace in
/-- G6, observed. -/
theorem systemMessage (L : AccountingLadderAdmitted c ca entry)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv notCreated
  have callerNe :
      (systemTransactionMessage benv target data).currentTarget = ca →
        (systemTransactionMessage benv target data).caller ≠ ca := by
    intro current
    rw [systemTransactionMessage_currentTarget] at current
    rw [systemTransactionMessage_caller]
    exact fun collide => systemNe (current.trans collide.symm)
  obtain ⟨steps, replay, observed⟩ := L.messageCall trace.message admitted
    (msgInv.runReady_of_call
      (systemTransactionMessage_target_isNone benv target data))
    callerNe (by simpa only [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hfork) sumNof blockIndex none
  rw [systemTransactionMessage_benv_state] at replay
  exact ⟨steps, replay, by simpa only [SystemMessageTrace.settledFrames,
    MessageCallTrace.settledFrames, ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq,
    ProcessMessageTrace.settledFrames] using observed⟩

open _root_.Blanc.ExecutionTrace in
/-- G7, observed. -/
theorem requests (L : AccountingLadderAdmitted c ca entry)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  obtain ⟨withdrawalSteps, withdrawalReplay, withdrawalObserved⟩ :=
    L.systemMessage trace.withdrawal admitted.withdrawal inv notCreated (by decide) sumNof hfork
      blockIndex
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    trace.withdrawal.benvInv_admitted_sem L.preserves hfork admitted.withdrawal ⟨inv, notCreated⟩
  have withdrawalSum :
      sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (trace.withdrawal.stateInv_and_sum_le_admitted_sem L.preserves hfork admitted.withdrawal ⟨inv, notCreated⟩).2
      sumNof
  obtain ⟨consolidationSteps, consolidationReplay, consolidationObserved⟩ :=
    L.systemMessage trace.consolidation admitted.consolidation withdrawalInv.state withdrawalInv.ca
      (by decide) withdrawalSum (by simpa only [Benv.withState] using hfork) blockIndex
  refine ⟨withdrawalSteps ++ consolidationSteps, ?_, ?_⟩
  · rw [RequestsTrace.state_eq_consolidationState trace]
    exact L.append withdrawalReplay consolidationReplay
  · rw [L.view.obs_append, withdrawalObserved, consolidationObserved]
    simp only [SystemMessageTrace.settledFrames, MessageCallTrace.settledFrames,
      ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq, ProcessMessageTrace.settledFrames,
      RequestsTrace.settledFrames, List.flatMap_append]

open _root_.Blanc.ExecutionTrace in
/-- G8, observed: direct withdrawals are observed as nothing. -/
theorem directWithdrawal (L : AccountingLadderAdmitted c ca entry)
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre) steps
      (L.carrier.ofState (processWithdrawalsState pre wds)) ∧
      L.view.obs steps = [] := by
  induction wds generalizing pre with
  | nil => exact ⟨[], L.carrier.nilOfEq rfl, L.view.obs_nil⟩
  | cons wd wds ih =>
      obtain ⟨headBound, tailBound⟩ := withdrawalCredit_bounds bound
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        L.carrier.ofAddBal_observed L.view (L.tag blockIndex none)
          (target := wd.recipient) headBound
      obtain ⟨tailSteps, tailReplay, tailObserved⟩ := ih _ tailBound
      refine ⟨headSteps ++ tailSteps, ?_, ?_⟩
      · rw [processWithdrawalsState_cons]
        exact L.append headReplay tailReplay
      · rw [L.view.obs_append, headObserved, tailObserved]
        rfl

open _root_.Blanc.ExecutionTrace in
/-- G9, observed: the segments are observed in `applyBody` order. -/
theorem body (L : AccountingLadderAdmitted c ca entry)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  -- (1) beacon roots
  obtain ⟨beaconSteps, beaconReplay, beaconObserved⟩ :=
    L.systemMessage trace.beacon admitted.beacon inv notCreated (by decide) openSum hfork blockIndex
  have beaconMeta :=
    trace.beacon.stateInv_and_sum_le_admitted_sem L.preserves hfork admitted.beacon ⟨inv, notCreated⟩
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beaconMeta.1, by simpa only [Benv.withState] using notCreated⟩
  have beaconSum :
      sum (benv.withState trace.beaconState).state.bal < 2 ^ 256 := by
    have le := beaconMeta.2
    simp only [Benv.withState] at le ⊢
    omega
  -- (2) history storage
  obtain ⟨historySteps, historyReplay, historyObserved⟩ :=
    L.systemMessage trace.history admitted.history beaconInv.state beaconInv.ca (by decide)
      beaconSum (by simpa only [Benv.withState] using hfork) blockIndex
  have historyMeta := trace.history.stateInv_and_sum_le_admitted_sem L.preserves
    (by simpa only [Benv.withState] using hfork) admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨historyMeta.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum :
      sum ((benv.withState trace.beaconState).withState
        trace.historyState).state.bal < 2 ^ 256 := by
    have le := historyMeta.2
    simp only [Benv.withState] at le beaconSum ⊢
    omega
  -- (3) the transaction list, by G5
  obtain ⟨txSteps, txReplay, txObserved⟩ :=
    L.transactionList trace.transactions admitted.transactions historyInv.state historyInv.ca
      historySum (by simpa only [Benv.withState] using hfork) blockIndex
  have txInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_sem L.preserves
      (by simpa only [Benv.withState] using hfork) admitted.transactions historySum historyInv
  have hforkTransaction : CoveredFork trace.transactionBenv.stat.fork := by
    rw [trace.transactions.stat_eq]
    simpa only [Benv.withState] using hfork
  -- (4) direct withdrawals, by G8
  have txBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    have hbeacon := beaconMeta.2
    have hhistory : sum trace.historyState.bal ≤ sum trace.beaconState.bal := by
      simpa only [Benv.withState] using historyMeta.2
    have htx : sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
      simpa [Benv.withState] using trace.transactions.sum_le
        (by simpa [Benv.withState] using hfork)
    omega
  obtain ⟨wdSteps, wdReplay, wdObserved⟩ :=
    L.directWithdrawal trace.transactionBenv.state wds txBound blockIndex
  have wdInv := benvInv_processWithdrawalsState_sem txInv txBound
  have wdSum :
      sum (trace.transactionBenv.withState (processWithdrawalsState
        trace.transactionBenv.state wds)).state.bal < 2 ^ 256 :=
    processWithdrawalsState_sum_nof txBound
  -- (5) request calls, by G7
  obtain ⟨requestSteps, requestReplay, requestObserved⟩ :=
    L.requests trace.requests admitted.requests wdInv.state wdInv.ca wdSum
      (by simpa only [Benv.withState] using hforkTransaction) blockIndex
  refine ⟨beaconSteps ++ (historySteps ++ (txSteps ++ (wdSteps ++ requestSteps))),
    L.append beaconReplay (L.append historyReplay
      (L.append txReplay (L.append wdReplay
        (by simpa only [Benv.withState, trace.requestState_eq] using requestReplay)))), ?_⟩
  simp only [L.view.obs_append, beaconObserved, historyObserved, txObserved,
    wdObserved, requestObserved, AppliedBodyTrace.settledFrames,
    List.flatMap_append, List.nil_append, List.append_assoc]

/-- G10, observed. -/
theorem configuredBlock (L : AccountingLadderAdmitted c ca entry)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  obtain ⟨steps, replay, observed⟩ :=
    L.body trace.bodyTrace admitted (trace.openingState ▸ inv)
      (trace.not_mem_openingCreatedAccounts ca) trace.openingBound trace.covered blockIndex
  refine ⟨steps, ?_, by simpa only [ExecutionTrace.ConfiguredBlockTrace.settledFrames,
    ExecutionTrace.AppliedBodyTrace.settledFrames, ExecutionTrace.SystemMessageTrace.settledFrames,
    ExecutionTrace.MessageCallTrace.settledFrames,
    ExecutionTrace.ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq,
    ExecutionTrace.ProcessMessageTrace.settledFrames, List.append_assoc,
    ExecutionTrace.RequestsTrace.settledFrames, List.flatMap_append] using observed⟩
  rw [trace.postState]
  rwa [trace.openingState] at replay

/-- G11, observed: a whole configured history replays with exactly the
observations of its settled frames, in chain order. -/
theorem configuredHistory (L : AccountingLadderAdmitted c ca entry) {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : history.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
        (L.carrier.ofState future.state) ∧
      L.view.obs steps = history.settledFrames.flatMap L.view.frameObs := by
  induction history with
  | refl hcfg hctx hid =>
      exact ⟨[], L.carrier.nilOfEq rfl, by simpa only [ExecutionTrace.ConfiguredHistoryTrace.settledFrames,
        List.flatMap_nil] using L.view.obs_nil⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay, priorObserved⟩ := ih admitted.1
      obtain ⟨blockSteps, blockReplay, blockObserved⟩ :=
        L.configuredBlock block admitted.2
          (prior.stateInv_admitted_sem L.preserves admitted.1 inv)
          block.block.header.number
      refine ⟨priorSteps ++ blockSteps, L.append priorReplay blockReplay, ?_⟩
      rw [L.view.obs_append, priorObserved, blockObserved]
      simp only [ExecutionTrace.ConfiguredBlockTrace.settledFrames,
        ExecutionTrace.AppliedBodyTrace.settledFrames,
        ExecutionTrace.SystemMessageTrace.settledFrames,
        ExecutionTrace.MessageCallTrace.settledFrames,
        ExecutionTrace.ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq,
        ExecutionTrace.ProcessMessageTrace.settledFrames, List.append_assoc,
        ExecutionTrace.RequestsTrace.settledFrames, List.flatMap_append,
        ExecutionTrace.ConfiguredHistoryTrace.settledFrames]


end AccountingLadderAdmitted

end ExecutionAccountingReplay

end Blanc
