import Blanc.ExecutionTransactionPrefix
import Blanc.ExecutionTraceAdmission

/-! Admission transport to an arbitrary transaction cut after both real
opening system calls. Neither withdrawals nor request calls are consumed. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Assigning transaction positions does not change the decoded list length. -/
theorem indexedTransactions_length {α : Type} (xs : List α) : xs.putIndex.length = xs.length := by
  have aux : ∀ k, (Jaune.List.putIndex.aux k xs).length = xs.length := by
    induction xs with
    | nil => intro k; rfl
    | cons x xs ih =>
        intro k
        simpa only [Jaune.List.putIndex.aux, List.length_cons] using congrArg Nat.succ (ih (k + 1))
  exact aux 0

/-- Taking the complete decoded list stops at the transaction boundary,
before any withdrawal credit or request call. -/
theorem AppliedBodyTrace.transactionPrefix_full_boundary
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (cut : trace.transactions.PrefixSplit trace.decodedTxs.length) :
    cut.benv = trace.transactionBenv ∧ cut.bout = trace.transactionBout := by
  have after := cut.suffix
  have dropped : trace.decodedTxs.putIndex.drop trace.decodedTxs.length = [] := by
    rw [← indexedTransactions_length trace.decodedTxs, List.drop_length]
  rw [dropped] at after
  exact ⟨after.nil_boundary.1.symm, after.nil_boundary.2.symm⟩

/-- Raw entered frames of the actual opening calls and selected transaction
prefix, including roots whose effects later roll back. -/
def AppliedBodyTrace.transactionPrefixFrames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) {n : Nat}
    (cut : trace.transactions.PrefixSplit n) : List Exec.Deriv :=
  trace.beacon.rawFrames ++ trace.history.rawFrames ++ cut.before.rawFrames

/-- A transaction cut keeps the body's actual fork. -/
theorem AppliedBodyTrace.transactionPrefix_covered
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) {n : Nat}
    (cut : trace.transactions.PrefixSplit n) (fork : CoveredFork benv.stat.fork) :
    CoveredFork cut.benv.stat.fork := by
  rw [cut.before.stat_eq]
  exact fork

/-- An arbitrary preserved contract invariant reaches the actual prefix
endpoint from body entry, using admission only for the entered prefix roots. -/
theorem AppliedBodyTrace.transactionPrefix_benvInv_admitted_sem
    {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) {n : Nat}
    (cut : trace.transactions.PrefixSplit n)
    (preserves : c.PreservesAdmitted ca entry) (fork : CoveredFork benv.stat.fork)
    (admitted : ∀ root ∈ trace.transactionPrefixFrames cut,
      root.sevm.currentTarget = ca → entry root.sevm root.devm)
    (bound : sum benv.state.bal < 2 ^ 256) (inv : c.BenvInv ca benv) :
    c.BenvInv ca cut.benv := by
  have beaconAdmission : trace.beacon.FrameAdmitted ca entry := by
    apply (trace.beacon.frameAdmitted_iff_rawFrames ca entry).2
    intro root member target
    exact admitted root (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))) target
  have historyAdmission : trace.history.FrameAdmitted ca entry := by
    apply (trace.history.frameAdmitted_iff_rawFrames ca entry).2
    intro root member target
    exact admitted root (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))) target
  have transactionAdmission : cut.before.FrameAdmitted ca entry := by
    apply (cut.before.frameAdmitted_iff_rawFrames ca entry).2
    intro root member target
    exact admitted root (List.mem_append.mpr (Or.inr member)) target
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_sem preserves fork beaconAdmission inv
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) := ⟨beacon.1, inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_sem
    preserves fork historyAdmission beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) := ⟨history.1, inv.ca⟩
  have historyBound : sum trace.historyState.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (le_trans history.2 beacon.2) bound
  exact cut.before.benvInv_admitted_sem preserves fork transactionAdmission historyBound historyInv

end Blanc.ExecutionTrace
