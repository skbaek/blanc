-- ProrataAccountingTransaction.lean : transaction-level accounting replay.

import Blanc.ProrataAccountingExec
import Blanc.ExecutionTransactionEffects

namespace Blanc

open Jaune

namespace Prorata

open _root_.Blanc.ExecutionTrace

/-- Two worlds that agree on PRORATA's own account agree on its accounting
projection: `ofState` reads nothing else. -/
private theorem ofState_congr_get
    {ca : Adr} {before after : State}
    (get : after.get ca = before.get ca) :
    AccountingSnapshot.ofState ca after = AccountingSnapshot.ofState ca before :=
  congrArg₂ AccountingSnapshot.mk
    (congrArg supplyN (congrArg Acct.stor get))
    (congrArg B256.toNat (congrArg Acct.bal get))

/-- The transaction's prepared message is accounting-ready unless it is a
CREATE aimed at PRORATA's own address, and that case cannot run any code: an
installed contract's compiled bytes make the create-collision test fire, so
the wrapper leaves the world exactly as it found it. -/
theorem TransactionTrace.messageAccountingReplay
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : prorataSpec.MsgInv ca trace.msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca trace.msg.benv.state) steps
        (AccountingSnapshot.ofState ca trace.messageState) := by
  have transfer : trace.msg.shouldTransferValue = true :=
    trace.msg_shouldTransferValue
  by_cases target : trace.msg.currentTarget = ca
  · cases receiver : trace.msg.target.isNone with
    | false =>
        exact retainedMessageCallAccountingReplay trace.message
          ⟨⟨msgInv, Or.inl receiver⟩, fun _ => msgInv.ne transfer⟩
          blockIndex transactionIndex
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
        exact ⟨[], ProrataAccountingReplay.nil_of_eq
          (congrArg (AccountingSnapshot.ofState ca) stateEq)⟩
  · exact retainedMessageCallAccountingReplay trace.message
      ⟨⟨msgInv, Or.inr target⟩, fun current => absurd current target⟩
      blockIndex transactionIndex

/-- Rung R2: one whole successful transaction realizes a complete PRORATA
accounting replay, from the world it opens on to its exact final state.

The transaction moves PRORATA's world in five places and each is discharged
without a new side condition.  The nonce bump and up-front gas debit cannot
touch PRORATA because a checked sender is never an installed contract; the
prepared message reuses rung R1; the sender gas refund misses PRORATA for the
same sender reason; the coinbase priority fee is the one place this rung
*adds* a step, and `ProrataAccountingReplay.of_addBal` supplies SF §5's
positive/zero split for a coinbase that may or may not be PRORATA itself; and
the final account-deletion fold never names an installed contract.  Both
credits are funded out of the transaction's own up-front debit, so neither
needs a wrap-around hypothesis. -/
theorem retainedTransactionAccountingReplay
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : prorataSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca benv.state) steps
        (AccountingSnapshot.ofState ca state) := by
  rcases trace.exists_stateChronology with ⟨chronology⟩
  have senderNe : trace.sender ≠ ca := trace.sender_ne inv notCreated
  let provenance : ProrataAccountingProvenance :=
    { blockIndex := blockIndex
      transactionIndex := transactionIndex
      framePath := []
      actor := none }
  -- (1) The nonce bump and up-front gas debit are invisible to PRORATA.
  have debitSnapshot :
      AccountingSnapshot.ofState ca trace.msg.benv.state =
        AccountingSnapshot.ofState ca benv.state := by
    rw [prepareMessage_benv trace.prepared]
    show AccountingSnapshot.ofState ca trace.debitState = _
    unfold AccountingSnapshot.ofState
    rw [trace.debitState_getStor_eq (ca := ca),
      trace.debitState_bal_eq senderNe]
  -- (2) The prepared message replays by rung R1.
  obtain ⟨messageSteps, messageReplay⟩ :=
    TransactionTrace.messageAccountingReplay trace (trace.msgInv inv notCreated)
      blockIndex transactionIndex
  rw [debitSnapshot] at messageReplay
  -- (3) and (4) The two gas credits, funded by the transaction's own debit.
  obtain ⟨refundBound, tipBound⟩ :=
    trace.settlement_sum_bounds chronology.refundCounter inv.side
  obtain ⟨refundSteps, refundReplay⟩ :=
    ProrataAccountingReplay.of_addBal (ca := ca) (target := trace.sender)
      (pre := trace.messageState)
      (value := trace.refundValue chronology.refundCounter)
      provenance refundBound
  obtain ⟨tipSteps, tipReplay⟩ :=
    ProrataAccountingReplay.of_addBal (ca := ca)
      (target := benv.stat.coinbase)
      (pre := trace.refundedState chronology.refundCounter)
      (value := trace.coinbaseValue chronology.refundCounter)
      provenance tipBound
  have refundReplay' :
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca trace.messageState) refundSteps
        (AccountingSnapshot.ofState ca
          (trace.refundedState chronology.refundCounter)) := refundReplay
  -- (5) The final deletion fold never names PRORATA.
  have deleteGet := foldl_destroyAccount_get_eq
    (state := trace.coinbaseState chronology.refundCounter)
    (trace.accountsToDelete_ne (prorataSpec_preserves ca) inv notCreated)
  have finalSnapshot :
      AccountingSnapshot.ofState ca state =
        AccountingSnapshot.ofState ca
          (trace.coinbaseState chronology.refundCounter) :=
    (congrArg (AccountingSnapshot.ofState ca) chronology.finalState_eq).trans
      (ofState_congr_get deleteGet)
  have tipReplay' :
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca
          (trace.refundedState chronology.refundCounter)) tipSteps
        (AccountingSnapshot.ofState ca state) := by
    rw [finalSnapshot]
    exact tipReplay
  exact ⟨messageSteps ++ (refundSteps ++ tipSteps),
    messageReplay.append (refundReplay'.append tipReplay')⟩

end Prorata

end Blanc
