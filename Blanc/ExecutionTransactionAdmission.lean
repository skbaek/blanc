import Blanc.ExecutionMessageAdmission
import Blanc.ExecutionTransactionEffects

/-!
# Trace-local admission through transactions

Admission is inherited only from the settled message trace actually retained
by a successful transaction.  Fee debit, gas credits, and final account
deletions remain ordinary deterministic envelope steps.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- The frame admission carried by a transaction is exactly the admission of
its retained settled message. -/
def TransactionTrace.FrameAdmitted
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  trace.message.FrameAdmitted ca entry

/-- Pointwise frame admission for the concrete transaction list retained by a
successful body execution. -/
def ApplyTransactionsTrace.FrameAdmitted
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .nil _ _ => True
  | .cons head tail =>
      head.FrameAdmitted ca entry ∧ tail.FrameAdmitted ca entry

open ContractSpec

variable {c : ContractSpec}

/-- An arbitrary contract invariant survives one retained transaction when
the concrete message frames selected by that transaction are admitted. -/
theorem TransactionTrace.benvInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca (benv.withState state) := by
  have msgInv : c.MsgInv ca trace.msg :=
    trace.msgInv inv.state inv.ca
  have msgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa [Benv.beginTransaction] using hfork
  have messageInv :=
    trace.message.stateInv_admitted preserves msgFork admitted msgInv
  rcases trace.exists_stateChronology hfork with ⟨chronology⟩
  have bounds :=
    trace.settlement_sum_bounds chronology.refundCounter sumNof hfork
  have refundInv : c.StateInv ca
      (trace.refundedState chronology.refundCounter) :=
    StateInv.addBal bounds.1 messageInv.1
  have coinbaseInv : c.StateInv ca
      (trace.coinbaseState chronology.refundCounter) :=
    StateInv.addBal bounds.2 refundInv
  have finalInv : c.StateInv ca
      (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.coinbaseState chronology.refundCounter)) :=
    StateInv.foldl_destroyAccount messageInv.2 coinbaseInv
  refine ⟨?_, by simpa [Benv.withState] using inv.ca⟩
  rw [chronology.finalState_eq]
  exact finalInv

/-- A retained transaction list threads trace-local admission and the ordinary
balance-sum bound through every successful transaction. -/
theorem ApplyTransactionsTrace.benvInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca finalBenv := by
  induction trace with
  | nil => exact inv
  | @cons index tx txs benv bout txState txBout finalBenv finalBout
      head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted preserves hfork admitted.1 sumNof inv
      have nextFork : CoveredFork (benv.withState txState).stat.fork := by
        change CoveredFork benv.stat.fork
        exact hfork
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 := by
        exact Nat.lt_of_le_of_lt
          (by simpa [Benv.withState] using
            processTransaction_sum_le head.result hfork.rules_stateGas_none)
          sumNof
      exact ih nextFork admitted.2 nextSum headInv

end ExecutionTrace

end Blanc
