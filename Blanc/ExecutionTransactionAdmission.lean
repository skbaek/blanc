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

/-- One fork-selected SELFDESTRUCT settlement step preserves an installed
contract that is not selected.  The Amsterdam clearing branch preserves the
complete balance function; the legacy branch uses the existing deletion
closure. -/
theorem StateInv.settleSelfdestructsStep
    {ca address : Adr} {state : State} (rules : ForkRules)
    (hne : address ≠ ca) (inv : c.StateInv ca state) :
    c.StateInv ca (ExecutionTrace.settleSelfdestructsStep rules state address) := by
  cases hgas : rules.stateGas with
  | none =>
      simpa only [ExecutionTrace.settleSelfdestructsStep, hgas] using
        inv.destroyAccount hne
  | some stateGas =>
      have hget :
          (ExecutionTrace.settleSelfdestructsStep rules state address).get ca =
            state.get ca :=
        ExecutionTrace.settleSelfdestructsStep_get_eq rules hne
      have hbal :
          (ExecutionTrace.settleSelfdestructsStep rules state address).bal =
            state.bal := by
        simp only [ExecutionTrace.settleSelfdestructsStep, hgas]
        exact ExecutionTrace.clearAccountPreservingBalance_bal state address
      refine ⟨?_, ?_, ?_⟩
      · rw [hget]
        exact inv.code
      · rw [hbal]
        exact inv.side
      · rw [hget]
        exact inv.inv

/-- The complete fork-selected SELFDESTRUCT settlement preserves an installed
contract omitted from the selected address list. -/
theorem StateInv.settleSelfdestructs
    {ca : Adr} {state : State} (rules : ForkRules) (addresses : List Adr)
    (hne : ∀ address ∈ addresses, address ≠ ca)
    (inv : c.StateInv ca state) :
    c.StateInv ca (Jaune.settleSelfdestructs rules addresses state) := by
  rw [ExecutionTrace.settleSelfdestructs_eq_foldl]
  induction addresses generalizing state with
  | nil => exact inv
  | cons address addresses ih =>
      rw [List.foldl_cons]
      exact ih
        (fun tail htail => hne tail (List.mem_cons_of_mem _ htail))
        (inv.settleSelfdestructsStep rules
          (hne address List.mem_cons_self))

/-- An arbitrary contract invariant survives one retained transaction when
the concrete message frames selected by that transaction are admitted. -/
theorem TransactionTrace.benvInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca (benv.withState state) := by
  have msgInv : c.MsgInv ca trace.msg :=
    trace.msgInv inv.state inv.ca
  have messageInv :=
    trace.message.stateInv_admitted preserves admitted msgInv
  rcases trace.exists_stateChronology with ⟨chronology⟩
  have bounds := trace.settlement_sum_bounds chronology.refundCounter sumNof
  have refundInv : c.StateInv ca
      (trace.refundedState chronology.refundCounter) :=
    StateInv.addBal bounds.1 messageInv.1
  have coinbaseInv : c.StateInv ca
      (trace.coinbaseState chronology.refundCounter) :=
    StateInv.addBal bounds.2 refundInv
  have finalInv : c.StateInv ca
      (settleSelfdestructs benv.beginTransaction.stat.rules
        trace.messageOut.accountsToDelete.toList
        (trace.coinbaseState chronology.refundCounter)) :=
    StateInv.settleSelfdestructs benv.beginTransaction.stat.rules
      trace.messageOut.accountsToDelete.toList messageInv.2 coinbaseInv
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
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca finalBenv := by
  induction trace with
  | nil => exact inv
  | @cons index tx txs benv bout txState txBout finalBenv finalBout
      head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted preserves admitted.1 sumNof inv
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 := by
        exact Nat.lt_of_le_of_lt
          (by simpa [Benv.withState] using processTransaction_sum_le head.result)
          sumNof
      exact ih admitted.2 nextSum headInv

end ExecutionTrace

end Blanc
