import Blanc.Corpus.Freeze.DepositCells
import Blanc.DepositRequestParser
import Blanc.ExecutionKeptReceiptLogs
import Blanc.ExecutionKeptRuntime
import Blanc.Lift.BeaconDeposit.LogOnly
import Blanc.Corpus.Proofs.DepositLogShape

/-! # The exact frozen covered-fork deposit parser statement -/

namespace Blanc.Composition.DepositParse

open Jaune Blanc Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

/-- Original indexed transactions at the installed deposit runtime produce exactly their
kept-frame request records, including after arbitrary withdrawals. -/
theorem parse_succeeds : ParseSucceeds CoveredFork := by
  intro benv txs bal final out senders roots wds fork installed transactions
  have hsg := fork.rules_stateGas_none
  have hbal := fork.rules_bal_none
  have entries := (transactions.runtime_of_runtimeSafety beaconInstalledCertH.runtimeSafety
    hsg (KeptFork.rules (Or.inl fork)).noSweep installed).2
  let keep : Log → Bool := fun log => decide
    (log.address = depositAddr ∧ log.topics[0]? = some depositEventSignatureHash)
  have address : ∀ log, keep log = true → log.address = depositAddr := by
    intro log selected
    exact (of_decide_eq_true selected).1
  obtain ⟨receipts, keys, lookups, logs⟩ := transactions.receipt_keptAt_logs
    address hsg hbal (putIndex_pairwise txs)
  have actualKeys : out.receiptKeys =
      txs.putIndex.map (fun item => BLT.toBytes (.bytes item.1.toBytes)) := by
    simpa only [BlockOutput.init, List.nil_append] using keys
  rw [← actualKeys] at lookups
  have accepted : ∀ log ∈ receipts.flatMap (fun receipt => receipt.2.logs.filter keep),
      ∃ record, extractDepositData log.data = .ok record := by
    intro log member
    rw [logs] at member
    obtain ⟨frame, frameMember, logMember⟩ := List.mem_flatMap.mp member
    obtain ⟨pcZero, target, code, forkEq, fresh⟩ := entries frame frameMember
    have appended := List.mem_of_mem_filter logMember
    rcases frame with ⟨pc, sevm, pre, outcome, executed, committed⟩
    cases outcome with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        have zero : pc = 0 := pcZero
        subst pc
        have covered : CoveredFork sevm.benvStat.fork := by
          rw [forkEq]
          exact fork
        obtain ⟨ev, event, extracted, length⟩ := successful_log_shape_any_data code covered
          fresh.1 fresh.2 executed log appended
        exact ⟨_, extracted⟩
  have parsed := parseDepositRequests_of_receipts receipts lookups accepted
  change parseDepositRequests out = .ok
    (((receipts.flatMap (fun receipt => receipt.2.logs.filter keep)).filterMap
      (fun log => match extractDepositData log.data with
        | .ok record => some record
        | .error _ => none)).flatten) at parsed
  rw [logs, List.filterMap_flatMap] at parsed
  rw [parseDepositRequests_withdrawalsPass]
  unfold frameRecords depositLogs frameLogs
  exact parsed

/-- Both positive halves of the exact frozen covered-fork D-S1 statement. -/
theorem d_s1 : D_S1 := ⟨Blanc.Corpus.Proofs.Deposit.log_shape, parse_succeeds⟩

end Blanc.Composition.DepositParse
