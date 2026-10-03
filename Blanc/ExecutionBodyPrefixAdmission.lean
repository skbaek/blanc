import Blanc.ExecutionBodyAdmission
import Blanc.ExecutionAccountingAdmission

/-! The exact request boundary of a retained body, before either checked
request call. Admission and opening bounds remain attached to that body. -/

namespace Blanc.ExecutionTrace

open Jaune

def AppliedBodyTrace.requestBenv {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) : Benv :=
  trace.transactionBenv.withState
    (processWithdrawalsState trace.transactionBenv.state wds)

/-- The transaction prefix retains the selected fork at the request boundary. -/
theorem AppliedBodyTrace.requestBenv_covered {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) (fork : CoveredFork benv.stat.fork) :
    CoveredFork trace.requestBenv.stat.fork := by
  change CoveredFork trace.transactionBenv.stat.fork
  rw [trace.transactions.stat_eq]
  exact fork

/-- Expose only the prefix invariant already transported by the admitted body
APIs; this does not consume either checked request outcome. -/
theorem AppliedBodyTrace.requestBenvInv_admitted_sem {c : ContractSpecSem}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput} (trace : AppliedBodyTrace benv txs wds state bout)
    (preserves : c.PreservesAdmitted ca entry) (fork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv) : c.BenvInv ca trace.requestBenv := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_sem
    preserves fork admitted.beacon inv
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_sem
    preserves fork admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, inv.ca⟩
  have historyBound : sum trace.historyState.bal < 2 ^ 256 := by
    have decrease := le_trans history.2 beacon.2
    omega
  have transactions := trace.transactions.benvInv_admitted_sem
    preserves fork admitted.transactions historyBound historyInv
  exact benvInv_processWithdrawalsState_sem transactions (trace.transactionBound bound fork)

end Blanc.ExecutionTrace
