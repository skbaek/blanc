import Blanc.ExecutionTransactionStateTrace

/-!
Contract-neutral selected state chronology for a successful Jaune transaction
under `stateGas = none`.

The selected gas, refund, and coinbase values route through the semantic
`settleTransactionGas` applied to the trace's retained fields, so the selected
quotient and validated floor flow through it.  The chronology retains the
up-front sender debit, the settled message stream, the selected sender gas
refund, the selected priority-fee credit, each final account deletion in fold
order, and finally the actual touched-account sweep in scan order, as distinct
ordered boundaries.  No contract-specific address is selected here.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Selected gas settlement: semantic `settleTransactionGas` applied to the
trace's retained fields. -/
def TransactionTrace.selectedGasSettlement
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : TransactionGasSettlement :=
  settleTransactionGas benv.stat.rules tx.gas trace.calldataFloorGasCost
    trace.messageOut.gasLeft trace.messageOut.stateGasLeft
    refundCounter trace.messageOut.stateGasUsed

/-- Selected sender refund installed after the settled message. -/
def TransactionTrace.selectedRefundValue
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : B256 :=
  ((trace.selectedGasSettlement refundCounter).gasLeft *
    trace.effectiveGasPrice).toB256

/-- Selected priority fee credited to the block coinbase. -/
def TransactionTrace.selectedCoinbaseValue
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : B256 :=
  ((trace.selectedGasSettlement refundCounter).gasUsed *
    (trace.effectiveGasPrice - benv.stat.baseFeePerGas)).toB256

def TransactionTrace.selectedRefundedState
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : State :=
  trace.messageState.addBal trace.sender
    (trace.selectedRefundValue refundCounter)

def TransactionTrace.selectedCoinbaseState
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : State :=
  (trace.selectedRefundedState refundCounter).addBal benv.stat.coinbase
    (trace.selectedCoinbaseValue refundCounter)

/-- The successful transaction's retained selected refund witness and exact
final-state equation, derived from the transaction result via the selected
final-state form under `stateGas = none`. -/
structure SelectedTransactionStateChronology
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') where
  refundCounter : Nat
  refundCounter_eq :
    Int.toNat? trace.messageOut.refundCounter = some refundCounter
  finalState_eq :
    state = sweepTouchedAccounts benv.stat.rules
      trace.messageOut.touchedAccounts.toList
      (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.selectedCoinbaseState refundCounter))

/-- Exact provenance for one retained selected transaction-level state
boundary. -/
inductive SelectedTransactionStateBoundaryOrigin where
  | debit {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace)
  | preparation {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace)
  | message {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace)
      (origin : MessageStateBoundaryOrigin)
  | refund {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace)
  | coinbase {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace)
  | deletion {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace) (address : Adr)
  | sweep {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : SelectedTransactionStateChronology trace) (address : Adr)

abbrev SelectedTransactionStateBoundary :=
  StateTransition SelectedTransactionStateBoundaryOrigin

/-- Retain every final account deletion in fold order. -/
def SelectedTransactionStateChronology.deletionBoundaries
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace) :
    State → List Adr → List SelectedTransactionStateBoundary
  | _, [] => []
  | before, address :: addresses =>
      { origin := .deletion chronology address
        before
        after := destroyAccount before address } ::
      chronology.deletionBoundaries (destroyAccount before address) addresses

/-- Retain every touched-account sweep attempt in scan order.  Identity
attempts are kept as events, recording the real scan; no deletion is invented
when the per-step test is false. -/
def SelectedTransactionStateChronology.sweepBoundariesAux
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace) :
    State → List Adr → List SelectedTransactionStateBoundary
  | _, [] => []
  | before, address :: addresses =>
      let after : State :=
        if accountExistsAndIsEmpty before address then
          destroyAccount before address
        else before
      { origin := .sweep chronology address
        before
        after } ::
      chronology.sweepBoundariesAux after addresses

/-- The touched-sweep suffix.  A disabled sweep contributes the empty suffix,
by the semantic identity. -/
def SelectedTransactionStateChronology.sweepBoundaries
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace)
    (before : State) (addresses : List Adr) :
    List SelectedTransactionStateBoundary :=
  if benv.stat.rules.settle.touchedSweep then
    chronology.sweepBoundariesAux before addresses
  else []

/-- Exact selected state chronology of one successful transaction: debit,
preparation, message, selected refund, selected coinbase, deletions in
`.toList` order, then the touched sweep in `.toList` order. -/
def SelectedTransactionStateChronology.stateBoundaries
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace) :
    List SelectedTransactionStateBoundary :=
  { origin := .debit chronology
    before := benv.state
    after := trace.debitState } ::
  { origin := .preparation chronology
    before := trace.debitState
    after := trace.msg.benv.state } ::
  ((trace.message.stateBoundaries.map
      (StateTransition.mapOrigin
        (SelectedTransactionStateBoundaryOrigin.message chronology))) ++
    { origin := .refund chronology
      before := trace.messageState
      after := trace.selectedRefundedState chronology.refundCounter } ::
    { origin := .coinbase chronology
      before := trace.selectedRefundedState chronology.refundCounter
      after := trace.selectedCoinbaseState chronology.refundCounter } ::
    (chronology.deletionBoundaries
      (trace.selectedCoinbaseState chronology.refundCounter)
      trace.messageOut.accountsToDelete.toList ++
    chronology.sweepBoundaries
      (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.selectedCoinbaseState chronology.refundCounter))
      trace.messageOut.touchedAccounts.toList))

/-- Every successful retained transaction under `stateGas = none` supplies its
exact selected refund witness. -/
theorem TransactionTrace.exists_selectedStateChronology
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (SelectedTransactionStateChronology trace) := by
  rcases trace.exists_selectedFinalStateForm hsg with
    ⟨refundCounter, refundCounterEq, finalStateEq⟩
  refine ⟨⟨refundCounter, refundCounterEq, ?_⟩⟩
  simpa only [selectedCoinbaseState, selectedRefundedState, selectedRefundValue,
    selectedCoinbaseValue, selectedGasSettlement] using
    finalStateEq

/-- The retained deletion suffix replays its `foldl` exactly. -/
private theorem SelectedTransactionStateChronology.deletionReplay
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace)
    (before : State) (addresses : List Adr) :
    StateReplay before
      (chronology.deletionBoundaries before addresses)
      (addresses.foldl destroyAccount before) := by
  induction addresses generalizing before with
  | nil => exact .nil _
  | cons address addresses ih =>
      exact .cons
        { origin := .deletion chronology address
          before
          after := destroyAccount before address }
        (ih (destroyAccount before address))

/-- The retained sweep scan replays its per-step conditional `foldl` exactly. -/
private theorem SelectedTransactionStateChronology.sweepReplayAux
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace)
    (before : State) (addresses : List Adr) :
    StateReplay before
      (chronology.sweepBoundariesAux before addresses)
      (addresses.foldl (fun state address =>
        if accountExistsAndIsEmpty state address then
          destroyAccount state address
        else state) before) := by
  induction addresses generalizing before with
  | nil => exact .nil _
  | cons address addresses ih =>
      exact .cons
        { origin := .sweep chronology address
          before
          after := if accountExistsAndIsEmpty before address then
            destroyAccount before address
          else before }
        (ih _)

/-- The retained sweep suffix replays the semantic `sweepTouchedAccounts`. -/
private theorem SelectedTransactionStateChronology.sweepReplay
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace)
    (before : State) (addresses : List Adr) :
    StateReplay before
      (chronology.sweepBoundaries before addresses)
      (sweepTouchedAccounts benv.stat.rules addresses before) := by
  cases h : benv.stat.rules.settle.touchedSweep with
  | true =>
      simp only [SelectedTransactionStateChronology.sweepBoundaries,
        sweepTouchedAccounts, h, ↓reduceIte]
      exact chronology.sweepReplayAux before addresses
  | false =>
      simp only [SelectedTransactionStateChronology.sweepBoundaries, h]
      rw [sweepTouchedAccounts_of_not_touchedSweep h]
      exact .nil _

/-- The retained selected transaction chronology is continuous from the
transaction's pre-state to its exact final state. -/
theorem SelectedTransactionStateChronology.stateReplay
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : SelectedTransactionStateChronology trace) :
    StateReplay benv.state chronology.stateBoundaries state := by
  let debit : SelectedTransactionStateBoundary :=
    { origin := .debit chronology
      before := benv.state
      after := trace.debitState }
  let preparation : SelectedTransactionStateBoundary :=
    { origin := .preparation chronology
      before := trace.debitState
      after := trace.msg.benv.state }
  let refund : SelectedTransactionStateBoundary :=
    { origin := .refund chronology
      before := trace.messageState
      after := trace.selectedRefundedState chronology.refundCounter }
  let coinbase : SelectedTransactionStateBoundary :=
    { origin := .coinbase chronology
      before := trace.selectedRefundedState chronology.refundCounter
      after := trace.selectedCoinbaseState chronology.refundCounter }
  have messageReplay := StateReplay.mapOrigin
    (SelectedTransactionStateBoundaryOrigin.message chronology)
    trace.message.stateReplay
  have deletionReplay := chronology.deletionReplay
    (trace.selectedCoinbaseState chronology.refundCounter)
    trace.messageOut.accountsToDelete.toList
  have sweepReplay := chronology.sweepReplay
    (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
      (trace.selectedCoinbaseState chronology.refundCounter))
    trace.messageOut.touchedAccounts.toList
  have settlementReplay :
      StateReplay trace.messageState
        (refund :: coinbase :: chronology.deletionBoundaries
          (trace.selectedCoinbaseState chronology.refundCounter)
          trace.messageOut.accountsToDelete.toList ++
          chronology.sweepBoundaries
            (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
              (trace.selectedCoinbaseState chronology.refundCounter))
            trace.messageOut.touchedAccounts.toList)
        (sweepTouchedAccounts benv.stat.rules
          trace.messageOut.touchedAccounts.toList
          (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
            (trace.selectedCoinbaseState chronology.refundCounter))) :=
    .cons refund (.cons coinbase (deletionReplay.append sweepReplay))
  rw [← chronology.finalState_eq] at settlementReplay
  exact .cons debit
    (.cons preparation (messageReplay.append settlementReplay))

end ExecutionTrace

end Blanc
