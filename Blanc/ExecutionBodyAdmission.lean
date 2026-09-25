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

open ContractSpecSem

variable {c : ContractSpecSem}

theorem systemTransactionMessage_msgInv_sem
    {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts) :
    c.MsgInv ca (systemTransactionMessage benv target data) := by
  have state : c.StateInv ca
      (systemTransactionMessage benv target data).benv.state := by
    simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using inv
  refine ⟨state, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [systemTransactionMessage, processSystemTransactionMsg,
        Benv.beginTransaction] using notCreated
    · exact fun empty => c.sem.ne_nil
        (state.code.symm.trans (congrArg some empty)) rfl
  · intro _ current
    have htarget : target = ca := by
      simpa [systemTransactionMessage, processSystemTransactionMsg] using
        current
    subst target
    simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using state.code
  · intro _ current
    have htarget : target = ca := by
      simpa [systemTransactionMessage, processSystemTransactionMsg] using
        current
    subst target
    simp [systemTransactionMessage, processSystemTransactionMsg]
  · intro transfer
    simp [systemTransactionMessage, processSystemTransactionMsg] at transfer
  · intro _ _
    simp [systemTransactionMessage, processSystemTransactionMsg]

theorem benvInv_processWithdrawalsState_sem
    {ca : Adr} {benv : Benv} {wds : List Withdrawal}
    (inv : c.BenvInv ca benv)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    c.BenvInv ca (benv.withState (processWithdrawalsState benv.state wds)) :=
  ⟨ContractSpecSem.processWithdrawalsState_preserves_inv ca benv.state wds bound
      inv.state,
    by simpa [Benv.withState] using inv.ca⟩

theorem SystemMessageTrace.stateInv_and_sum_le_admitted_sem
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv.state inv.ca
  have msgFork : CoveredFork (systemTransactionMessage benv target data).benv.stat.fork := by
    simpa [systemTransactionMessage, processSystemTransactionMsg, Benv.beginTransaction] using hfork
  have stateInv :=
    trace.message.stateInv_admitted_sem preserves msgFork admitted msgInv
  have sumLe := processMessageCall_sum_le
    (by simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction, BenvStat.rules] using hfork.rules_stateGas_none)
    trace.message.result
  refine ⟨stateInv.1, ?_⟩
  simpa [systemTransactionMessage, processSystemTransactionMsg,
    Benv.beginTransaction] using sumLe

theorem SystemMessageTrace.benvInv_admitted_sem
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca (benv.withState state) :=
  ⟨(trace.stateInv_and_sum_le_admitted_sem preserves hfork admitted inv).1,
    by simpa [Benv.withState] using inv.ca⟩

theorem RequestsTrace.stateInv_and_sum_le_admitted_sem
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted_sem
    preserves hfork admitted.withdrawal inv
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa [Benv.withState] using inv.ca⟩
  have consolidationFork : CoveredFork (benv.withState trace.withdrawalState).stat.fork := by
    simpa [Benv.withState] using hfork
  have consolidation := trace.consolidation.stateInv_and_sum_le_admitted_sem
    preserves consolidationFork admitted.consolidation withdrawalInv
  refine ⟨?_, ?_⟩
  · rw [trace.state_eq_consolidationState]
    exact consolidation.1
  · rw [trace.state_eq_consolidationState]
    exact le_trans consolidation.2 withdrawal.2

theorem AppliedBodyTrace.stateInv_admitted_sem
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_sem
    preserves hfork admitted.beacon inv
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_sem
    preserves (by simpa [Benv.withState] using hfork) admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa [Benv.withState] using beaconInv.ca⟩
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by
    have : sum trace.historyState.bal ≤ sum benv.state.bal :=
      le_trans (by simpa [Benv.withState] using history.2) beacon.2
    omega
  have hforkTransactions : CoveredFork trace.transactionBenv.stat.fork := by
    rw [trace.transactions.stat_eq]
    exact hfork
  have transactionsInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_sem preserves (by
      simpa [Benv.withState] using hfork) admitted.transactions
      historySum historyInv
  have transactionSum : sum trace.transactionBenv.state.bal ≤
      sum benv.state.bal := by
    exact le_trans (trace.transactions.sum_le (by simpa [Benv.withState] using hfork))
      (le_trans (by simpa [Benv.withState] using history.2) beacon.2)
  have withdrawalBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have withdrawalsInv : c.BenvInv ca
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)) :=
    benvInv_processWithdrawalsState_sem transactionsInv withdrawalBound
  rw [← trace.requestState_eq]
  exact (trace.requests.stateInv_and_sum_le_admitted_sem preserves
    (by simpa [Benv.withState] using hforkTransactions)
    admitted.requests withdrawalsInv).1

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
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have h := trace.stateInv_and_sum_le_admitted_sem (c := c.toSem)
    (preservesAdmitted_toSem c ca entry preserves) hfork admitted
    (benvInv_toSem inv)
  exact ⟨stateInv_ofSem h.1, h.2⟩

/-- Block-environment form of system-message preservation. -/
theorem SystemMessageTrace.benvInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca (benv.withState state) :=
  benvInv_ofSem (trace.benvInv_admitted_sem (c := c.toSem)
    (preservesAdmitted_toSem c ca entry preserves) hfork admitted
    (benvInv_toSem inv))

/-- Both checked request messages preserve the invariant and compose their
ordinary balance monotonicity facts. -/
theorem RequestsTrace.stateInv_and_sum_le_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have h := trace.stateInv_and_sum_le_admitted_sem (c := c.toSem)
    (preservesAdmitted_toSem c ca entry preserves) hfork admitted
    (benvInv_toSem inv)
  exact ⟨stateInv_ofSem h.1, h.2⟩

/-- A complete retained body preserves an arbitrary contract invariant when
all of its concrete interpreter traces are admitted.  The retained body bound
continues to discharge every balance-credit side condition. -/
theorem AppliedBodyTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state := by
  exact stateInv_ofSem (trace.stateInv_admitted_sem (c := c.toSem)
    (preservesAdmitted_toSem c ca entry preserves) hfork admitted bound
    (benvInv_toSem inv))

end ExecutionTrace

end Blanc
