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

end ExecutionTrace

namespace ExecutionAccountingReplay

/-! ## 2.2 One more account-local classifier -/

namespace ReplayCarrier

variable {ca : Adr}

/-- A direct world-state balance credit is one positive credit at `ca` or no
step at all. -/
theorem ofAddBal (C : ReplayCarrier ca) (tag : C.Tag)
    {target : Adr} {pre : State} {value : B256}
    (sum_nof : sum pre.bal + value.toNat < 2 ^ 256) :
    ∃ steps, C.Replay (C.ofState pre) steps
      (C.ofState (pre.addBal target value)) := by
  have storage_eq :
      (pre.addBal target value).getStor ca = pre.getStor ca := by
    show ((pre.setBal target (pre.bal target + value)).get ca).stor =
      (pre.get ca).stor
    rw [State.setBal_get_stor]
  apply C.ofStorageEqBalanceMono tag storage_eq
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
  root : ∀ (blockIndex : Nat) (transactionIndex : Option Nat)
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
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      exact L.carrier.ofStorageEqBalanceMono (L.tag blockIndex transactionIndex)
        (congrFun
          (_root_.Blanc.ExecutionTrace.ProcessMessage.none_ok_getStor_eq
            process) ca)
        (_root_.Blanc.ProcessMessage.targetBalanceMono_of_none process
          runReady.ready.ne sumNof)
  | @some pc sevm pre out run =>
      apply L.carrier.processMessage_of_body process runReady.ready.ne
        runReady.ready.val0 sumNof
      intro committed
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      exact L.root blockIndex transactionIndex run transfer evmEq committed
        runReady callerNe sumNof
-- mirrors ProrataAccountingExec.lean:632–655.

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
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      exact L.carrier.ofStorageEqBalanceMono (L.tag blockIndex transactionIndex)
        (congrFun
          (_root_.Blanc.ExecutionTrace.ProcessCreateMessage.none_ok_getStor_eq_of_empty
            process fresh) ca)
        (_root_.Blanc.ProcessCreateMessage.targetBalanceMono_of_none process
          runReady.ready.ne sumNof)
  | @some pc sevm pre out run =>
      apply L.carrier.processCreateMessage_of_body process runReady.ready.ne
        runReady.ready.val0 fresh sumNof
      intro committed
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
      exact L.root blockIndex transactionIndex run transfer evmEq committed
        (preparedInv.runReady_of_foreign preparedTargetNe)
        (fun target => absurd target preparedTargetNe) preparedSum
-- mirrors ProrataAccountingExec.lean:673–707.  The root caller clause is
-- vacuous at a foreign prepared target, so G2 takes no `callerNe`.

open _root_.Blanc.ExecutionTrace in
/-- G3.  The settled message-call wrapper (create collision, CREATE run, and
EIP-7702-normalized call). -/
theorem messageCall (L : AccountingLadder S ca)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) := by
  cases trace with
  | createCollision targetNone collision result =>
      have stateEq :=
        processMessageCall_createCollision_state_eq targetNone collision result
      exact L.carrier.ofStorageEqBalanceMono (L.tag blockIndex transactionIndex)
        (by rw [stateEq]) (by rw [stateEq])
  | createRun targetNone collision evm core inner result =>
      have targetNe : msg.currentTarget ≠ ca := by
        rcases runReady.codeOrForeign with call | foreign
        · exact Bool.noConfusion (targetNone.symm.trans call)
        · exact foreign
      have fresh := messageCreateCollision_false_getStor_eq_empty collision
      rw [processMessageCall_createRun_state_eq targetNone collision core result]
      exact L.processCreateMessage inner runReady sumNof targetNone targetNe
        fresh blockIndex transactionIndex
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm
      core inner result =>
      subst execMsgEq
      have stateEq :=
        processMessageCall_callRun_state_eq targetSome delegation rfl core
          result
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
      rw [stateEq, ← snapshotEq]
      exact L.processMessage inner execReady execCallerNe execSum
        blockIndex transactionIndex
-- mirrors ProrataAccountingExec.lean:726–779.

open _root_.Blanc.ExecutionTrace in
/-- G3'.  A transaction's prepared message, including the create-at-`ca` case,
which the collision test turns into a no-op. -/
theorem transactionMessage (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : S.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) := by
  have transfer : trace.msg.shouldTransferValue = true :=
    trace.msg_shouldTransferValue
  by_cases target : trace.msg.currentTarget = ca
  · cases receiver : trace.msg.target.isNone with
    | false =>
        exact L.messageCall trace.message (msgInv.runReady_of_call receiver)
          (fun _ => msgInv.ne transfer) sumNof blockIndex transactionIndex
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
            trace.message.result
        exact ⟨[], L.carrier.nilOfEq (congrArg L.carrier.ofState stateEq)⟩
  · exact L.messageCall trace.message (msgInv.runReady_of_foreign target)
      (fun current => absurd current target) sumNof blockIndex transactionIndex
-- mirrors ProrataAccountingTransaction.lean:37–61.

open _root_.Blanc.ExecutionTrace in
/-- G4.  One whole retained transaction. -/
theorem transaction (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  rcases trace.exists_stateChronology with ⟨chronology⟩
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
  obtain ⟨messageSteps, messageReplay⟩ :=
    L.transactionMessage trace (trace.msgInv inv notCreated)
      (trace.msg_sum_nof sumNof) blockIndex transactionIndex
  rw [debitSnapshot] at messageReplay
  -- (3), (4) the two gas credits, funded by the transaction's own debit
  obtain ⟨refundBound, tipBound⟩ :=
    trace.settlement_sum_bounds chronology.refundCounter sumNof
  obtain ⟨refundSteps, refundReplay⟩ :=
    L.carrier.ofAddBal (L.tag blockIndex transactionIndex)
      (target := trace.sender) (pre := trace.messageState)
      (value := trace.refundValue chronology.refundCounter) refundBound
  obtain ⟨tipSteps, tipReplay⟩ :=
    L.carrier.ofAddBal (L.tag blockIndex transactionIndex)
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
    (trace.accountsToDelete_ne L.preserves inv notCreated)
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
  exact ⟨messageSteps ++ (refundSteps ++ tipSteps),
    L.append messageReplay (L.append refundReplay' tipReplay')⟩
-- mirrors ProrataAccountingTransaction.lean:86–146; `inv.side` → `sumNof`.

open _root_.Blanc.ExecutionTrace in
/-- G5.  A retained transaction list. -/
theorem transactionList (L : AccountingLadder S ca)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) := by
  induction trace with
  | nil => exact ⟨[], L.carrier.nilOfEq rfl⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail
      ih =>
      obtain ⟨headSteps, headReplay⟩ :=
        L.transaction head inv notCreated sumNof blockIndex (some index)
      have next : S.BenvInv ca (benv.withState txState) :=
        head.benvInv L.preserves sumNof ⟨inv, notCreated⟩
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa [Benv.withState] using processTransaction_sum_le head.result)
          sumNof
      obtain ⟨tailSteps, tailReplay⟩ := ih next.state next.ca nextSum
      exact ⟨headSteps ++ tailSteps, L.append headReplay tailReplay⟩
-- mirrors ProrataAccountingBody.lean:31–45; the successor bound is
-- DripRealizedHistory.lean:147–149.

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
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  have msgInv : S.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv inv notCreated
  have callerNe :
      (systemTransactionMessage benv target data).currentTarget = ca →
        (systemTransactionMessage benv target data).caller ≠ ca := by
    intro current
    rw [systemTransactionMessage_currentTarget] at current
    rw [systemTransactionMessage_caller]
    exact fun collide => systemNe (current.trans collide.symm)
  have replay := L.messageCall trace.message
    (msgInv.runReady_of_call
      (systemTransactionMessage_target_isNone benv target data))
    callerNe sumNof blockIndex none
  rwa [systemTransactionMessage_benv_state] at replay
-- mirrors ProrataAccountingBody.lean:68–84.

open _root_.Blanc.ExecutionTrace in
/-- G7.  The two checked request calls. -/
theorem requests (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  obtain ⟨withdrawalSteps, withdrawalReplay⟩ :=
    L.systemMessage trace.withdrawal inv notCreated (by decide) sumNof
      blockIndex
  have withdrawalInv : S.BenvInv ca (benv.withState trace.withdrawalState) :=
    trace.withdrawal.benvInv L.preserves ⟨inv, notCreated⟩
  have withdrawalSum :
      sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (trace.withdrawal.stateInv_and_sum_le L.preserves ⟨inv, notCreated⟩).2
      sumNof
  obtain ⟨consolidationSteps, consolidationReplay⟩ :=
    L.systemMessage trace.consolidation withdrawalInv.state withdrawalInv.ca
      (by decide) withdrawalSum blockIndex
  refine ⟨withdrawalSteps ++ consolidationSteps, ?_⟩
  rw [RequestsTrace.state_eq_consolidationState trace]
  exact L.append withdrawalReplay consolidationReplay
-- mirrors ProrataAccountingBody.lean:99–112.

open _root_.Blanc.ExecutionTrace in
/-- G8.  The direct consensus withdrawals. -/
theorem directWithdrawal (L : AccountingLadder S ca)
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre) steps
      (L.carrier.ofState (processWithdrawalsState pre wds)) := by
  induction wds generalizing pre with
  | nil => exact ⟨[], L.carrier.nilOfEq rfl⟩
  | cons wd wds ih =>
      obtain ⟨headBound, tailBound⟩ := withdrawalCredit_bounds bound
      obtain ⟨headSteps, headReplay⟩ :=
        L.carrier.ofAddBal (L.tag blockIndex none) (target := wd.recipient)
          headBound
      obtain ⟨tailSteps, tailReplay⟩ := ih _ tailBound
      refine ⟨headSteps ++ tailSteps, ?_⟩
      rw [processWithdrawalsState_cons]
      exact L.append headReplay tailReplay
-- mirrors ProrataAccountingBody.lean:130–146.

open _root_.Blanc.ExecutionTrace in
/-- G9.  A whole successful block body, in `applyBody` order. -/
theorem body (L : AccountingLadder S ca)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  -- (1) beacon roots
  obtain ⟨beaconSteps, beaconReplay⟩ :=
    L.systemMessage trace.beacon inv notCreated (by decide) openSum blockIndex
  have beaconMeta :=
    trace.beacon.stateInv_and_sum_le L.preserves ⟨inv, notCreated⟩
  have beaconInv : S.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beaconMeta.1, by simpa [Benv.withState] using notCreated⟩
  have beaconSum :
      sum (benv.withState trace.beaconState).state.bal < 2 ^ 256 := by
    have le := beaconMeta.2
    simp only [Benv.withState] at le ⊢
    omega
  -- (2) history storage
  obtain ⟨historySteps, historyReplay⟩ :=
    L.systemMessage trace.history beaconInv.state beaconInv.ca (by decide)
      beaconSum blockIndex
  have historyMeta := trace.history.stateInv_and_sum_le L.preserves beaconInv
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
  obtain ⟨txSteps, txReplay⟩ :=
    L.transactionList trace.transactions historyInv.state historyInv.ca
      historySum blockIndex
  have txInv : S.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv L.preserves historySum historyInv
  -- (4) direct withdrawals, by G8
  have txBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    have hbeacon := beaconMeta.2
    have hhistory : sum trace.historyState.bal ≤ sum trace.beaconState.bal := by
      simpa [Benv.withState] using historyMeta.2
    have htx : sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
      simpa [Benv.withState] using trace.transactions.sum_le
    omega
  obtain ⟨wdSteps, wdReplay⟩ :=
    L.directWithdrawal trace.transactionBenv.state wds txBound blockIndex
  have wdInv := benvInv_processWithdrawalsState txInv txBound
  have wdSum :
      sum (trace.transactionBenv.withState (processWithdrawalsState
        trace.transactionBenv.state wds)).state.bal < 2 ^ 256 :=
    processWithdrawalsState_sum_nof txBound
  -- (5) request calls, by G7
  obtain ⟨requestSteps, requestReplay⟩ :=
    L.requests trace.requests wdInv.state wdInv.ca wdSum blockIndex
  exact ⟨beaconSteps ++ (historySteps ++ (txSteps ++ (wdSteps ++ requestSteps))),
    L.append beaconReplay (L.append historyReplay
      (L.append txReplay (L.append wdReplay requestReplay)))⟩
-- mirrors ProrataAccountingBody.lean:174–222; the three `.side` reads become
-- `openSum`/`beaconSum`/`historySum`, and the request-entry bound is the new
-- `processWithdrawalsState_sum_nof`.

/-- G10.  A whole configured block.  The word bound comes from the block's own
`openingBound`, so the rung asks only for the state invariant. -/
theorem configuredBlock (L : AccountingLadder S ca)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (inv : S.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) := by
  obtain ⟨steps, replay⟩ :=
    L.body trace.bodyTrace (trace.openingState ▸ inv)
      (trace.not_mem_openingCreatedAccounts ca) trace.openingBound blockIndex
  refine ⟨steps, ?_⟩
  rw [trace.postState]
  rwa [trace.openingState] at replay
-- mirrors ProrataAccountingHistory.lean:37–46.

/-- G11.  A whole configured history; each block is tagged with its header
number. -/
theorem configuredHistory (L : AccountingLadder S ca)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : S.StateInv ca checkpoint.state) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
      (L.carrier.ofState future.state) := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], L.carrier.nilOfEq rfl⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay⟩ := ih
      obtain ⟨blockSteps, blockReplay⟩ :=
        L.configuredBlock block (prior.stateInv L.preserves inv)
          block.block.header.number
      exact ⟨priorSteps ++ blockSteps, L.append priorReplay blockReplay⟩
-- mirrors ProrataAccountingHistory.lean:70–80.

end AccountingLadder

end ExecutionAccountingReplay

end Blanc
