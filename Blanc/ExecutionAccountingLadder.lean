-- ExecutionAccountingLadder.lean : the contract-neutral wrapper ladder over an
-- accounting replay.
--
-- `ExecutionAccountingReplay` owns the settlement seams of one retained
-- message.  Above them, every contract that interprets a retained history as
-- an ordered replay climbs the same ladder: message, CREATE, message-call
-- wrapper, transaction, transaction list, system message, request calls,
-- direct withdrawals, block body, configured block, configured history.  None
-- of those rungs is about a ledger.  A contract supplies an `AccountingLadder`
-- -- its account-local carrier, the carrier's composition law, the tag its
-- produced credit steps carry, the replay of one retained message root, and its
-- `ContractSpec` preservation -- and receives every rung at its own vocabulary.
--
-- The world word bound is an explicit premise up to the request rung and is
-- derived above it, because a general `ContractSpec.Side` need not be `SumNof`.

import Blanc.ExecutionAccountingReplay
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects
import Blanc.ExecutionTraceSettledFrames

namespace Blanc

open Jaune

/-! ## 2.1 Two word-bound transports the Execution layer lacks -/

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
-- mirrors DripRealizedHistory.lean:136–143 (the `head` case of
-- `TransactionMessageOccurrence.msg_sum_nof`) line for line.

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
-- the induction of ProrataAccountingBody.lean:123–146, keeping only the bound.

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
-- the `injection` of `prepareMessage_benv` (Ladder.lean:6347–6355); `prepareMessage` sets
-- `caller := tenv.stat.origin` (Jaune Transaction.lean:846) and `transactionTenv` sets `origin := sender`.

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
-- hoisted from Weth10HolderFlowResult.lean:669–682 (a contract module, not importable here); the
-- `addBal` step is the generic ladder's own `ofAddBal` storage line (G:80–84).

/-- G+4.  The block's withdrawal bound survives the body prefix. -/
theorem AppliedBodyTrace.transactionBound
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
  have beacon := processMessageCall_sum_le
    (by simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction, BenvStat.rules] using hfork.rules_stateGas_none)
    trace.beacon.message.result
  have history := processMessageCall_sum_le
    (by simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction, Benv.withState, BenvStat.rules] using
      hfork.rules_stateGas_none)
    trace.history.message.result
  have transactions := trace.transactions.sum_le (by
    simpa [Benv.withState] using hfork)
  simp only [systemTransactionMessage_benv_state, Benv.withState] at beacon history transactions
  omega
-- AppliedBodyTrace.sum_le_of_empty_withdrawals (ExecutionBodyEffects.lean:229–240), first three lines;
-- it is also the inline `txBound` of G:548–556 and PB:190–198, which may then use it.

end ExecutionTrace

namespace ExecutionAccountingReplay

/-! ## 2.2 One more account-local classifier -/

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
-- mirrors ProrataRealizedAccounting.lean:1052–1106; the positive/zero split is
-- delegated to `ofStorageEqBalanceMono` (ExecutionAccountingReplay.lean:473).


/-- A direct world-state balance credit is one positive credit at `ca` or no
step at all. -/
theorem ofAddBal (C : ReplayCarrier ca) (tag : C.Tag)
    {target : Adr} {pre : State} {value : B256}
    (sum_nof : sum pre.bal + value.toNat < 2 ^ 256) :
    ∃ steps, C.Replay (C.ofState pre) steps
      (C.ofState (pre.addBal target value)) := by
  exact (C.ofAddBal_observed (ReplayObservation.trivial C) tag sum_nof).imp
    fun _ replay => replay.1

end ReplayCarrier

/-! ## 2.3 The ladder interface -/

/-- Everything the wrapper ladder needs from one contract, and nothing else.

* `carrier` — the account-local replay interpretation;
* `append` — replays compose at a shared boundary (the one law of the replay
  relation the seams never needed);
* `tag` — the provenance a credit step produced at ladder level carries,
  given the block and transaction position (`Unit`-valued carriers ignore it);
* `root` — a committed retained execution at the EVM root of a successful
  message entry replays from the frame's entry boundary to its committed
  post-state, for every message that is run-ready for `S`, is not a direct
  self-call, and opens below the word bound.  This is exactly the shape of a
  contract's `lift_core` instance at `initEvm`;
* `preserves` — the contract's `ContractSpec` preservation, which the generic
  ladder lemmas consume to carry `S.StateInv` along the history. -/
structure AccountingLadder (S : ContractSpec) (ca : Adr) where
  carrier : ReplayCarrier ca
  append : ∀ {pre mid post : carrier.Snap} {left right : List carrier.Step},
    carrier.Replay pre left mid → carrier.Replay mid right post →
      carrier.Replay pre (left ++ right) post
  tag : Nat → Option Nat → carrier.Tag
  root : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entry : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution},
    Exec pc sevm pre out →
    msg.benvAfterTransfer = .ok entry →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry) →
    ∀ committed : Execution.commits out = true,
    S.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∃ steps, carrier.Replay (carrier.frameEntry sevm pre.state) steps
      (carrier.ofState (Execution.committedPost out committed).state)
  preserves : S.Preserves ca

/-! ## 2.3' The observed ladder

An `Observed` ladder is a ladder together with an observation of its carrier's
step lists and a root law that observes exactly the root's committed frames.
Every rung below is proved once, observed; the unobserved rungs of §2.4 are the
observed ones read through `Observed.trivial`, which observes nothing. -/

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
  | createRun _ noCollision => simp_all
  | callRun noTarget => simp_all

namespace AccountingLadder

/-- A ladder with an observation of its steps whose root replay observes
exactly the root's committed frames. -/
structure Observed {S : ContractSpec} {ca : Adr} (L : AccountingLadder S ca) where
  view : ReplayObservation L.carrier
  root : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entry : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out),
    msg.benvAfterTransfer = .ok entry →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry) →
    ∀ committed : Execution.commits out = true,
    S.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∃ steps, L.carrier.Replay (L.carrier.frameEntry sevm pre.state) steps
      (L.carrier.ofState (Execution.committedPost out committed).state) ∧
      view.obs steps = (Exec.committedFrames run).flatMap view.frameObs

namespace Observed

variable {S : ContractSpec} {ca : Adr} {L : AccountingLadder S ca}

/-- Every ladder is observed by the observation that sees nothing. -/
def trivial (L : AccountingLadder S ca) : L.Observed where
  view := ReplayObservation.trivial L.carrier
  root := by
    intro blockIndex transactionIndex msg entry pc sevm pre out run transfer
      evmEq committed runReady callerNe sumNof
    exact (L.root blockIndex transactionIndex run transfer evmEq committed
      runReady callerNe sumNof).imp fun _ replay =>
        ⟨replay, by simp [ReplayObservation.trivial]⟩

private theorem ite_flatMap {α β : Type} (c : Prop) [Decidable c]
    (l : List α) (f : α → List β) :
    (if c then l else []).flatMap f = if c then l.flatMap f else [] := by
  split <;> simp

/-- G1, observed. -/
theorem processMessage (O : L.Observed)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed O.view
          (L.tag blockIndex transactionIndex)
          (congrFun
            (_root_.Blanc.ExecutionTrace.ProcessMessage.none_ok_getStor_eq
              process) ca)
          (_root_.Blanc.ProcessMessage.targetBalanceMono_of_none process
            runReady.ready.ne sumNof)
      exact ⟨steps, replay, by simp [observed]⟩
  | @some pc sevm pre out run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.toSettlementCarrier.processMessage_of_body_observed
          O.view.obs O.view.obs_nil process runReady.ready.ne
          runReady.ready.val0 sumNof fun committed =>
            O.root blockIndex transactionIndex run transfer evmEq committed
              runReady callerNe sumNof
      refine ⟨steps, replay, ?_⟩
      rw [observed]
      simp only [ExecutionTrace.ProcessMessageTrace.settledFrames, ite_flatMap]
-- mirrors ProrataAccountingExec.lean:632–655.

/-- G2, observed. -/
theorem processCreateMessage (O : L.Observed)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed O.view
          (L.tag blockIndex transactionIndex)
          (congrFun
            (_root_.Blanc.ExecutionTrace.ProcessCreateMessage.none_ok_getStor_eq_of_empty
              process fresh) ca)
          (_root_.Blanc.ProcessCreateMessage.targetBalanceMono_of_none process
            runReady.ready.ne sumNof)
      exact ⟨steps, replay, by simp [observed]⟩
  | @some pc sevm pre out run =>
      have preparedInv :=
        runReady.ready.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe :
          (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by
          simpa [processCreateMessage.msg, Msg.withBenv] using target)
      have preparedSum :
          sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [_root_.Blanc.processCreateMessage_msg_bal_eq]
        exact sumNof
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.toSettlementCarrier.processCreateMessage_of_body_observed
          O.view.obs O.view.obs_nil process runReady.ready.ne
          runReady.ready.val0 fresh sumNof fun committed =>
            O.root blockIndex transactionIndex run transfer evmEq committed
              (preparedInv.runReady_of_foreign preparedTargetNe)
              (fun target => absurd target preparedTargetNe) preparedSum
      refine ⟨steps, replay, ?_⟩
      rw [observed]
      simp only [ExecutionTrace.ProcessCreateMessageTrace.settledFrames,
        ite_flatMap]
-- mirrors ProrataAccountingExec.lean:673–707.  The root caller clause is
-- vacuous at a foreign prepared target, so G2 takes no `callerNe`.

open _root_.Blanc.ExecutionTrace in
/-- G3, observed. -/
theorem messageCall (O : L.Observed)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  cases trace with
  | createCollision targetNone collision result =>
      have stateEq :=
        processMessageCall_createCollision_state_eq targetNone collision result hfork
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed O.view
          (L.tag blockIndex transactionIndex)
          (pre := msg.benv.state) (post := state)
          (by rw [stateEq]) (by rw [stateEq])
      exact ⟨steps, replay, by simp [observed]⟩
  | createRun targetNone collision evm core inner result =>
      have targetNe : msg.currentTarget ≠ ca := by
        rcases runReady.codeOrForeign with call | foreign
        · exact Bool.noConfusion (targetNone.symm.trans call)
        · exact foreign
      have fresh := messageCreateCollision_false_getStor_eq_empty collision
      obtain ⟨steps, replay, observed⟩ :=
        O.processCreateMessage inner runReady sumNof targetNone targetNe
          fresh blockIndex transactionIndex
      refine ⟨steps, ?_, by simpa using observed⟩
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
          S.MessageRunReady ca (messageCallExecutionMessage delegated) := by
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
      obtain ⟨steps, replay, observed⟩ :=
        O.processMessage inner execReady execCallerNe execSum
          blockIndex transactionIndex
      refine ⟨steps, ?_, by simpa using observed⟩
      rw [stateEq, ← snapshotEq]
      exact replay
-- mirrors ProrataAccountingExec.lean:726–779.

open _root_.Blanc.ExecutionTrace in
/-- G3', observed. -/
theorem transactionMessage (O : L.Observed)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : S.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  have transfer : trace.msg.shouldTransferValue = true :=
    trace.msg_shouldTransferValue
  have msgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa [Benv.beginTransaction] using hfork
  simp only [TransactionTrace.settledFrames]
  by_cases target : trace.msg.currentTarget = ca
  · cases receiver : trace.msg.target.isNone with
    | false =>
        exact O.messageCall trace.message (msgInv.runReady_of_call receiver)
          (fun _ => msgInv.ne transfer) msgFork sumNof blockIndex transactionIndex
    | true =>
        have collision : messageCreateCollision trace.msg = true := by
          cases test : messageCreateCollision trace.msg with
          | false =>
              exact absurd target
                (ContractSpec.StateInv.ne_of_messageCreateCollision_false
                  msgInv.state test)
          | true => rfl
        have stateEq : trace.messageState = trace.msg.benv.state :=
          processMessageCall_createCollision_state_eq receiver collision
            trace.message.result msgFork
        refine ⟨[], L.carrier.nilOfEq (congrArg L.carrier.ofState stateEq), ?_⟩
        rw [trace.message.settledFrames_eq_nil_of_collision receiver collision]
        simpa using O.view.obs_nil
  · exact O.messageCall trace.message (msgInv.runReady_of_foreign target)
      (fun current => absurd current target) msgFork sumNof blockIndex transactionIndex
-- mirrors ProrataAccountingTransaction.lean:37–61.

open _root_.Blanc.ExecutionTrace in
/-- G4, observed: the two gas credits are observed as nothing. -/
theorem transaction (O : L.Observed)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  rcases trace.exists_stateChronology hfork with ⟨chronology⟩
  have senderNe : trace.sender ≠ ca := trace.sender_ne inv notCreated
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
    O.transactionMessage trace (trace.msgInv inv notCreated)
      (trace.msg_sum_nof sumNof) hfork blockIndex transactionIndex
  rw [debitSnapshot] at messageReplay
  -- (3), (4) the two gas credits, funded by the transaction's own debit
  obtain ⟨refundBound, tipBound⟩ :=
    trace.settlement_sum_bounds chronology.refundCounter sumNof hfork
  obtain ⟨refundSteps, refundReplay, refundObserved⟩ :=
    L.carrier.ofAddBal_observed O.view (L.tag blockIndex transactionIndex)
      (target := trace.sender) (pre := trace.messageState)
      (value := trace.refundValue chronology.refundCounter) refundBound
  obtain ⟨tipSteps, tipReplay, tipObserved⟩ :=
    L.carrier.ofAddBal_observed O.view (L.tag blockIndex transactionIndex)
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
    (trace.accountsToDelete_ne L.preserves inv notCreated hfork)
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
  rw [O.view.obs_append, O.view.obs_append, messageObserved, refundObserved,
    tipObserved]
  simp
-- mirrors ProrataAccountingTransaction.lean:86–146; `inv.side` → `sumNof`.

open _root_.Blanc.ExecutionTrace in
/-- G5, observed. -/
theorem transactionList (O : L.Observed)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  induction trace with
  | nil =>
      exact ⟨[], L.carrier.nilOfEq rfl, by simpa using O.view.obs_nil⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail
      ih =>
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        O.transaction head inv notCreated sumNof hfork blockIndex (some index)
      have next : S.BenvInv ca (benv.withState txState) :=
        head.benvInv L.preserves sumNof ⟨inv, notCreated⟩ hfork
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa [Benv.withState] using
            processTransaction_sum_le head.result hfork.rules_stateGas_none)
          sumNof
      obtain ⟨tailSteps, tailReplay, tailObserved⟩ :=
        ih next.state next.ca nextSum (by simpa [Benv.withState] using hfork)
      refine ⟨headSteps ++ tailSteps, L.append headReplay tailReplay, ?_⟩
      rw [O.view.obs_append, headObserved, tailObserved]
      simp
-- mirrors ProrataAccountingBody.lean:31–45; the successor bound is
-- DripRealizedHistory.lean:147–149.

open _root_.Blanc.ExecutionTrace in
/-- G6, observed. -/
theorem systemMessage (O : L.Observed)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  have msgInv : S.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv inv notCreated
  have callerNe :
      (systemTransactionMessage benv target data).currentTarget = ca →
        (systemTransactionMessage benv target data).caller ≠ ca := by
    intro current
    rw [systemTransactionMessage_currentTarget] at current
    rw [systemTransactionMessage_caller]
    exact fun collide => systemNe (current.trans collide.symm)
  obtain ⟨steps, replay, observed⟩ := O.messageCall trace.message
    (msgInv.runReady_of_call
      (systemTransactionMessage_target_isNone benv target data))
    callerNe (by simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hfork) sumNof blockIndex none
  rw [systemTransactionMessage_benv_state] at replay
  exact ⟨steps, replay, by simpa using observed⟩
-- mirrors ProrataAccountingBody.lean:68–84.

open _root_.Blanc.ExecutionTrace in
/-- G7, observed. -/
theorem requests (O : L.Observed)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  obtain ⟨withdrawalSteps, withdrawalReplay, withdrawalObserved⟩ :=
    O.systemMessage trace.withdrawal inv notCreated (by decide) sumNof hfork
      blockIndex
  have withdrawalInv : S.BenvInv ca (benv.withState trace.withdrawalState) :=
    trace.withdrawal.benvInv L.preserves ⟨inv, notCreated⟩ hfork
  have withdrawalSum :
      sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (trace.withdrawal.stateInv_and_sum_le L.preserves ⟨inv, notCreated⟩ hfork).2
      sumNof
  obtain ⟨consolidationSteps, consolidationReplay, consolidationObserved⟩ :=
    O.systemMessage trace.consolidation withdrawalInv.state withdrawalInv.ca
      (by decide) withdrawalSum (by simpa [Benv.withState] using hfork) blockIndex
  refine ⟨withdrawalSteps ++ consolidationSteps, ?_, ?_⟩
  · rw [RequestsTrace.state_eq_consolidationState trace]
    exact L.append withdrawalReplay consolidationReplay
  · rw [O.view.obs_append, withdrawalObserved, consolidationObserved]
    simp
-- mirrors ProrataAccountingBody.lean:99–112.

open _root_.Blanc.ExecutionTrace in
/-- G8, observed: direct withdrawals are observed as nothing. -/
theorem directWithdrawal (O : L.Observed)
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre) steps
      (L.carrier.ofState (processWithdrawalsState pre wds)) ∧
      O.view.obs steps = [] := by
  induction wds generalizing pre with
  | nil => exact ⟨[], L.carrier.nilOfEq rfl, O.view.obs_nil⟩
  | cons wd wds ih =>
      obtain ⟨headBound, tailBound⟩ := withdrawalCredit_bounds bound
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        L.carrier.ofAddBal_observed O.view (L.tag blockIndex none)
          (target := wd.recipient) headBound
      obtain ⟨tailSteps, tailReplay, tailObserved⟩ := ih _ tailBound
      refine ⟨headSteps ++ tailSteps, ?_, ?_⟩
      · rw [processWithdrawalsState_cons]
        exact L.append headReplay tailReplay
      · rw [O.view.obs_append, headObserved, tailObserved]
        rfl
-- mirrors ProrataAccountingBody.lean:130–146.

open _root_.Blanc.ExecutionTrace in
/-- G9, observed: the segments are observed in `applyBody` order. -/
theorem body (O : L.Observed)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  -- (1) beacon roots
  obtain ⟨beaconSteps, beaconReplay, beaconObserved⟩ :=
    O.systemMessage trace.beacon inv notCreated (by decide) openSum hfork blockIndex
  have beaconMeta :=
    trace.beacon.stateInv_and_sum_le L.preserves ⟨inv, notCreated⟩ hfork
  have beaconInv : S.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beaconMeta.1, by simpa [Benv.withState] using notCreated⟩
  have beaconSum :
      sum (benv.withState trace.beaconState).state.bal < 2 ^ 256 := by
    have le := beaconMeta.2
    simp only [Benv.withState] at le ⊢
    omega
  -- (2) history storage
  obtain ⟨historySteps, historyReplay, historyObserved⟩ :=
    O.systemMessage trace.history beaconInv.state beaconInv.ca (by decide)
      beaconSum (by simpa [Benv.withState] using hfork) blockIndex
  have historyMeta := trace.history.stateInv_and_sum_le L.preserves beaconInv
    (by simpa [Benv.withState] using hfork)
  have historyInv : S.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨historyMeta.1, by simpa [Benv.withState] using beaconInv.ca⟩
  have historySum :
      sum ((benv.withState trace.beaconState).withState
        trace.historyState).state.bal < 2 ^ 256 := by
    have le := historyMeta.2
    simp only [Benv.withState] at le beaconSum ⊢
    omega
  -- (3) the transaction list, by G5
  obtain ⟨txSteps, txReplay, txObserved⟩ :=
    O.transactionList trace.transactions historyInv.state historyInv.ca
      historySum (by simpa [Benv.withState] using hfork) blockIndex
  have txInv : S.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv L.preserves historySum historyInv
      (by simpa [Benv.withState] using hfork)
  have hforkTransaction : CoveredFork trace.transactionBenv.stat.fork := by
    rw [trace.transactions.stat_eq]
    simpa [Benv.withState] using hfork
  -- (4) direct withdrawals, by G8
  have txBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    have hbeacon := beaconMeta.2
    have hhistory : sum trace.historyState.bal ≤ sum trace.beaconState.bal := by
      simpa [Benv.withState] using historyMeta.2
    have htx : sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
      simpa [Benv.withState] using trace.transactions.sum_le
        (by simpa [Benv.withState] using hfork)
    omega
  obtain ⟨wdSteps, wdReplay, wdObserved⟩ :=
    O.directWithdrawal trace.transactionBenv.state wds txBound blockIndex
  have wdInv := benvInv_processWithdrawalsState txInv txBound
  have wdSum :
      sum (trace.transactionBenv.withState (processWithdrawalsState
        trace.transactionBenv.state wds)).state.bal < 2 ^ 256 :=
    processWithdrawalsState_sum_nof txBound
  -- (5) request calls, by G7
  obtain ⟨requestSteps, requestReplay, requestObserved⟩ :=
    O.requests trace.requests wdInv.state wdInv.ca wdSum
      (by simpa [Benv.withState] using hforkTransaction) blockIndex
  refine ⟨beaconSteps ++ (historySteps ++ (txSteps ++ (wdSteps ++ requestSteps))),
    L.append beaconReplay (L.append historyReplay
      (L.append txReplay (L.append wdReplay
        (by simpa [Benv.withState, trace.requestState_eq] using requestReplay)))), ?_⟩
  simp only [O.view.obs_append, beaconObserved, historyObserved, txObserved,
    wdObserved, requestObserved, AppliedBodyTrace.settledFrames,
    List.flatMap_append, List.nil_append, List.append_assoc]
-- mirrors ProrataAccountingBody.lean:174–222; the three `.side` reads become
-- `openSum`/`beaconSum`/`historySum`, and the request-entry bound is the new
-- `processWithdrawalsState_sum_nof`.

/-- G10, observed. -/
theorem configuredBlock (O : L.Observed)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (inv : S.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  obtain ⟨steps, replay, observed⟩ :=
    O.body trace.bodyTrace (trace.openingState ▸ inv)
      (trace.not_mem_openingCreatedAccounts ca) trace.openingBound trace.covered blockIndex
  refine ⟨steps, ?_, by simpa using observed⟩
  rw [trace.postState]
  rwa [trace.openingState] at replay
-- mirrors ProrataAccountingHistory.lean:37–46.

/-- G11, observed: a whole configured history replays with exactly the
observations of its settled frames, in chain order. -/
theorem configuredHistory (O : L.Observed) {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : S.StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
        (L.carrier.ofState future.state) ∧
      O.view.obs steps = history.settledFrames.flatMap O.view.frameObs := by
  induction history with
  | refl hcfg hctx hid =>
      exact ⟨[], L.carrier.nilOfEq rfl, by simpa using O.view.obs_nil⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay, priorObserved⟩ := ih
      obtain ⟨blockSteps, blockReplay, blockObserved⟩ :=
        O.configuredBlock block (prior.stateInv L.preserves inv hcov)
          block.block.header.number
      refine ⟨priorSteps ++ blockSteps, L.append priorReplay blockReplay, ?_⟩
      rw [O.view.obs_append, priorObserved, blockObserved]
      simp
-- mirrors ProrataAccountingHistory.lean:70–80.

end Observed

end AccountingLadder

namespace AccountingLadder

variable {S : ContractSpec} {ca : Adr}

/-! ## 2.4 The rungs -/

/-- G1.  One retained CALL message. -/
theorem processMessage (L : AccountingLadder S ca)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) := by
  exact ((Observed.trivial L).processMessage trace runReady callerNe sumNof blockIndex transactionIndex).imp
    fun _ replay => replay.1

/-- G2.  One retained CREATE constructor at a fresh foreign address. -/
theorem processCreateMessage (L : AccountingLadder S ca)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) := by
  exact ((Observed.trivial L).processCreateMessage trace runReady sumNof targetNone targetNe fresh blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G3.  The settled message-call wrapper (create collision, CREATE run, and
EIP-7702-normalized call). -/
theorem messageCall (L : AccountingLadder S ca)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork msg.benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).messageCall trace runReady callerNe hfork sumNof blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G3'.  A transaction's prepared message, including the create-at-`ca` case,
which the collision test turns into a no-op. -/
theorem transactionMessage (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : S.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) := by
  exact ((Observed.trivial L).transactionMessage trace msgInv sumNof hfork blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G4.  One whole retained transaction. -/
theorem transaction (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).transaction trace inv notCreated sumNof hfork blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G5.  A retained transaction list. -/
theorem transactionList (L : AccountingLadder S ca)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) := by
  exact ((Observed.trivial L).transactionList trace inv notCreated sumNof hfork blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G6.  One retained system message. -/
theorem systemMessage (L : AccountingLadder S ca)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).systemMessage trace inv notCreated systemNe sumNof hfork blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G7.  The two checked request calls. -/
theorem requests (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).requests trace inv notCreated sumNof hfork blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G8.  The direct consensus withdrawals. -/
theorem directWithdrawal (L : AccountingLadder S ca)
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre) steps
      (L.carrier.ofState (processWithdrawalsState pre wds)) := by
  exact ((Observed.trivial L).directWithdrawal pre wds bound blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G9.  A whole successful block body, in `applyBody` order. -/
theorem body (L : AccountingLadder S ca)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).body trace inv notCreated bound hfork blockIndex).imp
    fun _ replay => replay.1

/-- G10.  A whole configured block.  The word bound comes from the block's own
`openingBound`, so the rung asks only for the state invariant. -/
theorem configuredBlock (L : AccountingLadder S ca)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (inv : S.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) := by
  exact ((Observed.trivial L).configuredBlock trace inv blockIndex).imp
    fun _ replay => replay.1

/-- G11.  A whole configured history; each block is tagged with its header
number. -/
theorem configuredHistory (L : AccountingLadder S ca)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : S.StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
      (L.carrier.ofState future.state) := by
  exact ((Observed.trivial L).configuredHistory history inv hcov).imp
    fun _ replay => replay.1

end AccountingLadder

/-! ## 2.5 The block-structured history carrier

`L.TraceRealizes cfg root steps future` supplements configured reachability from
`root` with the replay steps the chain actually produced: in chain order, one
retained `ConfiguredBlockTrace` per imported block together with that block's
own replay segment, the whole step list being their concatenation.  The
carrier names no contract; the two contract facts it needs -- the root's
reflexive configured reach and the contract invariant at the root -- enter as
arguments of the lemmas that use them. -/

namespace AccountingLadder

variable {S : ContractSpec} {ca : Adr}

inductive TraceRealizes (L : AccountingLadder S ca) (cfg : ChainConfig)
    (root : BlockChain) : List L.carrier.Step → BlockChain → Prop where
  | refl : TraceRealizes L cfg root [] root
  | step {current future : BlockChain}
      {priorSteps blockSteps : List L.carrier.Step}
      (prior : TraceRealizes L cfg root priorSteps current)
      (block : _root_.Blanc.ExecutionTrace.ConfiguredBlockTrace cfg current future)
      (replay : L.carrier.Replay (L.carrier.ofState current.state) blockSteps
        (L.carrier.ofState future.state)) :
      TraceRealizes L cfg root (priorSteps ++ blockSteps) future
-- mirrors ProrataAccountingHistory.lean:96–107.

/-- Every retained configured history from an invariant-satisfying root is
realized, with exactly the observations of its settled frames in chain order. -/
theorem Observed.traceRealizes_of_configuredHistoryTrace
    {L : AccountingLadder S ca} (O : L.Observed)
    {cfg : ChainConfig} {root future : BlockChain}
    (inv : S.StateInv ca root.state)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg root future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.TraceRealizes cfg root steps future ∧
      O.view.obs steps = history.settledFrames.flatMap O.view.frameObs := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], .refl, by simpa using O.view.obs_nil⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorRealizes, priorObserved⟩ := ih
      obtain ⟨blockSteps, blockReplay, blockObserved⟩ :=
        O.configuredBlock block (prior.stateInv L.preserves inv hcov)
          block.block.header.number
      refine ⟨priorSteps ++ blockSteps, .step priorRealizes block blockReplay, ?_⟩
      rw [O.view.obs_append, priorObserved, blockObserved]
      simp
-- mirrors ProrataAccountingHistory.lean:146–159, carrying the observation.

namespace TraceRealizes

/-- Every realized trace projects to the configured chain reach it replays. -/
theorem toReachUsing {L : AccountingLadder S ca} {cfg : ChainConfig}
    {root future : BlockChain} {steps : List L.carrier.Step}
    (rootReach : BlockChain.ReachUsing cfg root root)
    (realizes : L.TraceRealizes cfg root steps future) :
    BlockChain.ReachUsing cfg root future := by
  induction realizes with
  | refl => exact rootReach
  | step prior block replay ih => exact .step ih block.bound block.transition
-- mirrors ProrataAccountingHistory.lean:116–123; `root.reflReach` → `rootReach`.

/-- The realized steps are one connected replay from the root to the
continuation, the per-block segments concatenated in chain order. -/
theorem toReplay {L : AccountingLadder S ca} {cfg : ChainConfig}
    {root future : BlockChain} {steps : List L.carrier.Step}
    (realizes : L.TraceRealizes cfg root steps future) :
    L.carrier.Replay (L.carrier.ofState root.state) steps
      (L.carrier.ofState future.state) := by
  induction realizes with
  | refl => exact L.carrier.nil _
  | step prior block replay ih => exact L.append ih replay
-- mirrors ProrataAccountingHistory.lean:128–137.

/-- Every retained configured history from an invariant-satisfying root is
realized; each block is tagged with its own header number. -/
theorem of_configuredHistoryTrace (L : AccountingLadder S ca)
    {cfg : ChainConfig} {root future : BlockChain}
    (inv : S.StateInv ca root.state)
    (history : _root_.Blanc.ExecutionTrace.ConfiguredHistoryTrace cfg root future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.TraceRealizes cfg root steps future := by
  exact ((Observed.trivial L).traceRealizes_of_configuredHistoryTrace inv
    history hcov).imp fun _ realizes => realizes.1

/-- Configured reachability from an invariant-satisfying root is never more
permissive than the carrier. -/
theorem exists_of_reachUsing (L : AccountingLadder S ca)
    {cfg : ChainConfig} {root future : BlockChain}
    (inv : S.StateInv ca root.state)
    (reach : BlockChain.ReachUsing cfg root future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.TraceRealizes cfg root steps future := by
  rcases _root_.Blanc.ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing
    reach (by intro _ _ _ _ _ hfork; exact hcov _ _ hfork) with ⟨history⟩
  exact of_configuredHistoryTrace L inv history hcov
-- mirrors ProrataAccountingHistory.lean:167–173.

end TraceRealizes

end AccountingLadder

end ExecutionAccountingReplay

end Blanc
