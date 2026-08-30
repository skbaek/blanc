import Blanc.ExecutionMessageStateTrace

/-!
Contract-neutral state chronology for a successful Jaune transaction.

The chronology retains the up-front sender debit, the settled message stream,
the sender gas refund, the priority-fee credit, and each final account
deletion as distinct ordered boundaries.  No contract-specific address is
selected here.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Charged gas after refund and calldata-floor accounting. -/
def TransactionTrace.chargedGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : Nat :=
  max (tx.gas - trace.messageOut.gasLeft -
      min ((tx.gas - trace.messageOut.gasLeft) / 5) refundCounter)
    trace.calldataFloorGasCost

/-- Sender refund installed after the settled message. -/
def TransactionTrace.refundValue
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : B256 :=
  ((tx.gas - trace.chargedGas refundCounter) *
    trace.effectiveGasPrice).toB256

/-- Priority fee credited to the block coinbase. -/
def TransactionTrace.coinbaseValue
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : B256 :=
  (trace.chargedGas refundCounter *
    (trace.effectiveGasPrice - benv.stat.baseFeePerGas)).toB256

def TransactionTrace.refundedState
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : State :=
  trace.messageState.addBal trace.sender (trace.refundValue refundCounter)

def TransactionTrace.coinbaseState
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat) : State :=
  (trace.refundedState refundCounter).addBal benv.stat.coinbase
    (trace.coinbaseValue refundCounter)

/-- The successful transaction's retained refund witness and exact final-state
equation. -/
structure TransactionStateChronology
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') where
  refundCounter : Nat
  refundCounter_eq :
    Int.toNat? trace.messageOut.refundCounter = some refundCounter
  finalState_eq :
    state = trace.messageOut.accountsToDelete.toList.foldl destroyAccount
      (trace.coinbaseState refundCounter)

/-- Exact provenance for one retained transaction-level state boundary. -/
inductive TransactionStateBoundaryOrigin where
  | debit {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : TransactionStateChronology trace)
  | preparation {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : TransactionStateChronology trace)
  | message {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : TransactionStateChronology trace)
      (origin : MessageStateBoundaryOrigin)
  | refund {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : TransactionStateChronology trace)
  | coinbase {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : TransactionStateChronology trace)
  | deletion {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      {trace : TransactionTrace benv bout tx index state bout'}
      (chronology : TransactionStateChronology trace) (address : Adr)

abbrev TransactionStateBoundary :=
  StateTransition TransactionStateBoundaryOrigin

/-- Retain every final account deletion in fold order. -/
def TransactionStateChronology.deletionBoundaries
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : TransactionStateChronology trace) :
    State → List Adr → List TransactionStateBoundary
  | _, [] => []
  | before, address :: addresses =>
      { origin := .deletion chronology address
        before
        after := destroyAccount before address } ::
      chronology.deletionBoundaries (destroyAccount before address) addresses

/-- Exact state chronology of one successful transaction. -/
def TransactionStateChronology.stateBoundaries
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : TransactionStateChronology trace) :
    List TransactionStateBoundary :=
  { origin := .debit chronology
    before := benv.state
    after := trace.debitState } ::
  { origin := .preparation chronology
    before := trace.debitState
    after := trace.msg.benv.state } ::
  ((trace.message.stateBoundaries.map
      (StateTransition.mapOrigin
        (TransactionStateBoundaryOrigin.message chronology))) ++
    { origin := .refund chronology
      before := trace.messageState
      after := trace.refundedState chronology.refundCounter } ::
    { origin := .coinbase chronology
      before := trace.refundedState chronology.refundCounter
      after := trace.coinbaseState chronology.refundCounter } ::
    chronology.deletionBoundaries
      (trace.coinbaseState chronology.refundCounter)
      trace.messageOut.accountsToDelete.toList)

/-- Every successful retained transaction supplies its exact refund witness. -/
theorem TransactionTrace.exists_stateChronology
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    Nonempty (TransactionStateChronology trace) := by
  rcases trace.exists_finalStateForm with
    ⟨refundCounter, refundCounterEq, finalStateEq⟩
  refine ⟨⟨refundCounter, refundCounterEq, ?_⟩⟩
  simpa [TransactionTrace.coinbaseState,
    TransactionTrace.refundedState, TransactionTrace.refundValue,
    TransactionTrace.coinbaseValue, TransactionTrace.chargedGas] using
    finalStateEq

/-- The retained deletion suffix replays its `foldl` exactly. -/
private theorem TransactionStateChronology.deletionReplay
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : TransactionStateChronology trace)
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

/-- The retained transaction chronology is continuous from the transaction's
pre-state to its exact final state. -/
theorem TransactionStateChronology.stateReplay
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    (chronology : TransactionStateChronology trace) :
    StateReplay benv.state chronology.stateBoundaries state := by
  let debit : TransactionStateBoundary :=
    { origin := .debit chronology
      before := benv.state
      after := trace.debitState }
  let preparation : TransactionStateBoundary :=
    { origin := .preparation chronology
      before := trace.debitState
      after := trace.msg.benv.state }
  let refund : TransactionStateBoundary :=
    { origin := .refund chronology
      before := trace.messageState
      after := trace.refundedState chronology.refundCounter }
  let coinbase : TransactionStateBoundary :=
    { origin := .coinbase chronology
      before := trace.refundedState chronology.refundCounter
      after := trace.coinbaseState chronology.refundCounter }
  have messageReplay := StateReplay.mapOrigin
    (TransactionStateBoundaryOrigin.message chronology)
    trace.message.stateReplay
  have deletionReplay := chronology.deletionReplay
    (trace.coinbaseState chronology.refundCounter)
    trace.messageOut.accountsToDelete.toList
  have settlementReplay :
      StateReplay trace.messageState
        (refund :: coinbase :: chronology.deletionBoundaries
          (trace.coinbaseState chronology.refundCounter)
          trace.messageOut.accountsToDelete.toList)
        (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
          (trace.coinbaseState chronology.refundCounter)) :=
    .cons refund (.cons coinbase deletionReplay)
  rw [← chronology.finalState_eq] at settlementReplay
  exact .cons debit
    (.cons preparation (messageReplay.append settlementReplay))

end ExecutionTrace

end Blanc
