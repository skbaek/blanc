import Blanc.ExecutionTransactionAdmission
import Blanc.ExecutionBodyEffects

/-!
# Trace-local admission through block bodies

The body carrier already retains every system message and normal transaction
in semantic order.  These predicates and transports require admission only
for those concrete interpreter executions; withdrawals and other direct state
steps retain their ordinary invariant proofs.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Admission for the settled message retained by one system transaction. -/
def SystemMessageTrace.FrameAdmitted
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  trace.message.FrameAdmitted ca entry

/-- Admission for both checked request-system messages, in execution order. -/
structure RequestsTrace.FrameAdmitted
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop where
  withdrawal : trace.withdrawal.FrameAdmitted ca entry
  consolidation : trace.consolidation.FrameAdmitted ca entry

/-- Admission for every interpreter-bearing component of one applied body. -/
structure AppliedBodyTrace.FrameAdmitted
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop where
  beacon : trace.beacon.FrameAdmitted ca entry
  history : trace.history.FrameAdmitted ca entry
  transactions : trace.transactions.FrameAdmitted ca entry
  requests : trace.requests.FrameAdmitted ca entry

open ContractSpec

variable {c : ContractSpec}

/-- A retained system message preserves an arbitrary contract invariant and
cannot increase total balance under trace-local admission. -/
theorem SystemMessageTrace.stateInv_and_sum_le_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv inv.state inv.ca
  have stateInv :=
    trace.message.stateInv_admitted preserves admitted msgInv
  have sumLe := processMessageCall_sum_le trace.message.result
  refine ⟨stateInv.1, ?_⟩
  simpa [systemTransactionMessage, processSystemTransactionMsg,
    Benv.beginTransaction] using sumLe

/-- Block-environment form of system-message preservation. -/
theorem SystemMessageTrace.benvInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca (benv.withState state) :=
  ⟨(trace.stateInv_and_sum_le_admitted preserves admitted inv).1,
    by simpa [Benv.withState] using inv.ca⟩

/-- Both checked request messages preserve the invariant and compose their
ordinary balance monotonicity facts. -/
theorem RequestsTrace.stateInv_and_sum_le_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted
    preserves admitted.withdrawal inv
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa [Benv.withState] using inv.ca⟩
  have consolidation := trace.consolidation.stateInv_and_sum_le_admitted
    preserves admitted.consolidation withdrawalInv
  refine ⟨?_, ?_⟩
  · rw [trace.state_eq_consolidationState]
    exact consolidation.1
  · rw [trace.state_eq_consolidationState]
    exact le_trans consolidation.2 withdrawal.2

/-- A complete retained body preserves an arbitrary contract invariant when
all of its concrete interpreter traces are admitted.  The retained body bound
continues to discharge every balance-credit side condition. -/
theorem AppliedBodyTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted
    preserves admitted.beacon inv
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted
    preserves admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa [Benv.withState] using beaconInv.ca⟩
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by
    have : sum trace.historyState.bal ≤ sum benv.state.bal :=
      le_trans (by simpa [Benv.withState] using history.2) beacon.2
    omega
  have transactionsInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted preserves admitted.transactions
      historySum historyInv
  have transactionSum : sum trace.transactionBenv.state.bal ≤
      sum benv.state.bal := by
    exact le_trans trace.transactions.sum_le
      (le_trans (by simpa [Benv.withState] using history.2) beacon.2)
  have withdrawalBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have withdrawalsInv : c.BenvInv ca
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)) :=
    benvInv_processWithdrawalsState transactionsInv withdrawalBound
  exact (trace.requests.stateInv_and_sum_le_admitted preserves
    admitted.requests withdrawalsInv).1

end ExecutionTrace

end Blanc
