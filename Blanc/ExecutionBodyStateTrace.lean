import Blanc.ExecutionTransactionStateTrace

/-!
Contract-neutral state chronology for Jaune system messages, transaction
lists, direct withdrawals, request messages, and complete applied bodies.

This module composes the lower retained traces without interpreting any
contract address.  Every boundary remains tied to the exact body trace that
selected it, and the final theorem replays from the block pre-state to the
exact successful `applyBody` state.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-! ## System messages -/

inductive SystemMessageStateBoundaryOrigin where
  | preparation {benv : Benv} {target : Adr} {data : Bytes}
      {state : State} {out : MsgCallOutput}
      (trace : SystemMessageTrace benv target data state out)
  | message {benv : Benv} {target : Adr} {data : Bytes}
      {state : State} {out : MsgCallOutput}
      (trace : SystemMessageTrace benv target data state out)
      (origin : MessageStateBoundaryOrigin)

abbrev SystemMessageStateBoundary :=
  StateTransition SystemMessageStateBoundaryOrigin

def SystemMessageTrace.stateBoundaries
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List SystemMessageStateBoundary :=
  { origin := .preparation trace
    before := benv.state
    after := (systemTransactionMessage benv target data).benv.state } ::
  trace.message.stateBoundaries.map
    (StateTransition.mapOrigin
      (SystemMessageStateBoundaryOrigin.message trace))

theorem SystemMessageTrace.stateReplay
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    StateReplay benv.state trace.stateBoundaries state := by
  let preparation : SystemMessageStateBoundary :=
    { origin := .preparation trace
      before := benv.state
      after := (systemTransactionMessage benv target data).benv.state }
  have messageReplay := StateReplay.mapOrigin
    (SystemMessageStateBoundaryOrigin.message trace)
    trace.message.stateReplay
  exact .cons preparation messageReplay

/-! ## Transaction lists -/

/-- Refund witnesses for every transaction in one retained transaction list. -/
inductive ApplyTransactionsStateChronology :
    {txs : List (Nat × Tx)} →
    {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) → Type
  | nil (benv : Benv) (bout : BlockOutput) :
      ApplyTransactionsStateChronology (.nil benv bout)
  | cons {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput}
      {txState : State} {txBout : BlockOutput}
      {finalBenv : Benv} {finalBout : BlockOutput}
      {head : TransactionTrace benv bout tx index txState txBout}
      {tail : ApplyTransactionsTrace txs (benv.withState txState) txBout
        finalBenv finalBout}
      (headChronology : TransactionStateChronology head)
      (tailChronology : ApplyTransactionsStateChronology tail) :
      ApplyTransactionsStateChronology (.cons head tail)

def ApplyTransactionsStateChronology.stateBoundaries
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    (chronology : ApplyTransactionsStateChronology trace) :
    List TransactionStateBoundary :=
  match chronology with
  | .nil _ _ => []
  | .cons head tail => head.stateBoundaries ++ tail.stateBoundaries

theorem ApplyTransactionsTrace.exists_stateChronology
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    Nonempty (ApplyTransactionsStateChronology trace) := by
  induction trace with
  | nil benv bout => exact ⟨.nil benv bout⟩
  | cons head tail ih =>
      rcases head.exists_stateChronology with ⟨headChronology⟩
      rcases ih with ⟨tailChronology⟩
      exact ⟨.cons headChronology tailChronology⟩

theorem ApplyTransactionsStateChronology.stateReplay
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    (chronology : ApplyTransactionsStateChronology trace) :
    StateReplay benv.state chronology.stateBoundaries finalBenv.state := by
  induction chronology with
  | nil benv _ => exact .nil benv.state
  | cons head tail ih => exact head.stateReplay.append ih

/-! ## Direct withdrawals -/

structure DirectWithdrawalStateBoundaryOrigin where
  withdrawal : Withdrawal

abbrev DirectWithdrawalStateBoundary :=
  StateTransition DirectWithdrawalStateBoundaryOrigin

/-- One direct-withdrawal balance credit over an abstract base state. -/
def directWithdrawalStateBoundary
    (before : State) (withdrawal : Withdrawal) :
    DirectWithdrawalStateBoundary :=
  { origin := ⟨withdrawal⟩
    before
    after := before.addBal withdrawal.recipient
      (withdrawal.amount * (10 ^ 9).toB256) }

theorem directWithdrawalStateBoundary_before
    (before : State) (withdrawal : Withdrawal) :
    (directWithdrawalStateBoundary before withdrawal).before = before := rfl

theorem directWithdrawalStateBoundary_after
    (before : State) (withdrawal : Withdrawal) :
    (directWithdrawalStateBoundary before withdrawal).after =
      before.addBal withdrawal.recipient
        (withdrawal.amount * (10 ^ 9).toB256) := rfl

def directWithdrawalStateBoundaries :
    State → List Withdrawal → List DirectWithdrawalStateBoundary
  | _, [] => []
  | before, withdrawal :: withdrawals =>
      directWithdrawalStateBoundary before withdrawal ::
      directWithdrawalStateBoundaries
        (directWithdrawalStateBoundary before withdrawal).after withdrawals

theorem directWithdrawalStateBoundaries_nil (before : State) :
    directWithdrawalStateBoundaries before [] = [] := rfl

theorem directWithdrawalStateBoundaries_cons
    (before : State) (withdrawal : Withdrawal)
    (withdrawals : List Withdrawal) :
    directWithdrawalStateBoundaries before (withdrawal :: withdrawals) =
      directWithdrawalStateBoundary before withdrawal ::
      directWithdrawalStateBoundaries
        (directWithdrawalStateBoundary before withdrawal).after
        withdrawals := rfl

theorem processWithdrawalsState_nil (before : State) :
    processWithdrawalsState before [] = before := rfl

theorem processWithdrawalsState_cons
    (before : State) (withdrawal : Withdrawal)
    (withdrawals : List Withdrawal) :
    processWithdrawalsState before (withdrawal :: withdrawals) =
      processWithdrawalsState
        (before.addBal withdrawal.recipient
          (withdrawal.amount * (10 ^ 9).toB256)) withdrawals := rfl

theorem directWithdrawalStateReplay
    (before : State) (withdrawals : List Withdrawal) :
    StateReplay before (directWithdrawalStateBoundaries before withdrawals)
      (processWithdrawalsState before withdrawals) := by
  induction withdrawals generalizing before with
  | nil =>
      rw [directWithdrawalStateBoundaries_nil,
        processWithdrawalsState_nil]
      exact .nil _
  | cons withdrawal withdrawals ih =>
      rw [directWithdrawalStateBoundaries_cons,
        processWithdrawalsState_cons]
      let event := directWithdrawalStateBoundary before withdrawal
      have rest := ih event.after
      have replay := StateReplay.cons event rest
      have beforeEq : event.before = before :=
        directWithdrawalStateBoundary_before before withdrawal
      have afterEq : event.after = before.addBal withdrawal.recipient
          (withdrawal.amount * (10 ^ 9).toB256) :=
        directWithdrawalStateBoundary_after before withdrawal
      rw [beforeEq, afterEq] at replay
      exact replay

/-! ## Request messages -/

inductive RequestsStateBoundaryOrigin where
  | withdrawal {benv : Benv} {bout : BlockOutput}
      {state : State} {bout' : BlockOutput}
      (trace : RequestsTrace benv bout state bout')
      (origin : SystemMessageStateBoundaryOrigin)
  | consolidation {benv : Benv} {bout : BlockOutput}
      {state : State} {bout' : BlockOutput}
      (trace : RequestsTrace benv bout state bout')
      (origin : SystemMessageStateBoundaryOrigin)

abbrev RequestsStateBoundary := StateTransition RequestsStateBoundaryOrigin

def RequestsTrace.stateBoundaries
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    List RequestsStateBoundary :=
  trace.withdrawal.stateBoundaries.map
      (StateTransition.mapOrigin
        (RequestsStateBoundaryOrigin.withdrawal trace)) ++
    trace.consolidation.stateBoundaries.map
      (StateTransition.mapOrigin
        (RequestsStateBoundaryOrigin.consolidation trace))

theorem RequestsTrace.stateReplay
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    StateReplay benv.state trace.stateBoundaries state := by
  have withdrawalReplay := StateReplay.mapOrigin
    (RequestsStateBoundaryOrigin.withdrawal trace)
    trace.withdrawal.stateReplay
  have consolidationReplay := StateReplay.mapOrigin
    (RequestsStateBoundaryOrigin.consolidation trace)
    trace.consolidation.stateReplay
  have replay := withdrawalReplay.append consolidationReplay
  exact replay.castPost trace.state_eq_consolidationState.symm

/-! ## Complete bodies -/

/-- The only additional witness needed above an `AppliedBodyTrace` is the
successful transaction list's sequence of refund counters. -/
structure AppliedBodyStateChronology
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) where
  transactions : ApplyTransactionsStateChronology trace.transactions

inductive AppliedBodyStateBoundaryOrigin where
  | beacon {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      {trace : AppliedBodyTrace benv txs wds state bout}
      (chronology : AppliedBodyStateChronology trace)
      (origin : SystemMessageStateBoundaryOrigin)
  | history {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      {trace : AppliedBodyTrace benv txs wds state bout}
      (chronology : AppliedBodyStateChronology trace)
      (origin : SystemMessageStateBoundaryOrigin)
  | transaction {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      {trace : AppliedBodyTrace benv txs wds state bout}
      (chronology : AppliedBodyStateChronology trace)
      (origin : TransactionStateBoundaryOrigin)
  | withdrawal {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      {trace : AppliedBodyTrace benv txs wds state bout}
      (chronology : AppliedBodyStateChronology trace)
      (origin : DirectWithdrawalStateBoundaryOrigin)
  | request {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      {trace : AppliedBodyTrace benv txs wds state bout}
      (chronology : AppliedBodyStateChronology trace)
      (origin : RequestsStateBoundaryOrigin)

abbrev AppliedBodyStateBoundary :=
  StateTransition AppliedBodyStateBoundaryOrigin

def AppliedBodyStateChronology.stateBoundaries
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {trace : AppliedBodyTrace benv txs wds state bout}
    (chronology : AppliedBodyStateChronology trace) :
    List AppliedBodyStateBoundary :=
  trace.beacon.stateBoundaries.map
      (StateTransition.mapOrigin
        (AppliedBodyStateBoundaryOrigin.beacon chronology)) ++
    trace.history.stateBoundaries.map
      (StateTransition.mapOrigin
        (AppliedBodyStateBoundaryOrigin.history chronology)) ++
    chronology.transactions.stateBoundaries.map
      (StateTransition.mapOrigin
        (AppliedBodyStateBoundaryOrigin.transaction chronology)) ++
    (directWithdrawalStateBoundaries trace.transactionBenv.state wds).map
      (StateTransition.mapOrigin
        (AppliedBodyStateBoundaryOrigin.withdrawal chronology)) ++
    trace.requests.stateBoundaries.map
      (StateTransition.mapOrigin
        (AppliedBodyStateBoundaryOrigin.request chronology))

theorem AppliedBodyTrace.exists_stateChronology
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    Nonempty (AppliedBodyStateChronology trace) := by
  rcases trace.transactions.exists_stateChronology with
    ⟨transactions⟩
  exact ⟨⟨transactions⟩⟩

/-- Complete successful block-body state replay, in exact semantic order. -/
theorem AppliedBodyStateChronology.stateReplay
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {trace : AppliedBodyTrace benv txs wds state bout}
    (chronology : AppliedBodyStateChronology trace) :
    StateReplay benv.state chronology.stateBoundaries state := by
  have beaconReplay := StateReplay.mapOrigin
    (AppliedBodyStateBoundaryOrigin.beacon chronology)
    trace.beacon.stateReplay
  have historyReplay := StateReplay.mapOrigin
    (AppliedBodyStateBoundaryOrigin.history chronology)
    trace.history.stateReplay
  have transactionReplay := StateReplay.mapOrigin
    (AppliedBodyStateBoundaryOrigin.transaction chronology)
    chronology.transactions.stateReplay
  have withdrawalReplay := StateReplay.mapOrigin
    (AppliedBodyStateBoundaryOrigin.withdrawal chronology)
    (directWithdrawalStateReplay trace.transactionBenv.state wds)
  have requestReplay := StateReplay.mapOrigin
    (AppliedBodyStateBoundaryOrigin.request chronology)
    trace.requests.stateReplay
  have replay := beaconReplay.append
    (historyReplay.append
      (transactionReplay.append
        (withdrawalReplay.append requestReplay)))
  simpa only [AppliedBodyStateChronology.stateBoundaries,
    List.append_assoc] using replay

end ExecutionTrace

end Blanc
