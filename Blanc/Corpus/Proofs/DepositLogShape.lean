import Blanc.Corpus.Freeze.DepositCells
import Blanc.ExecutionKeptFresh
import Blanc.Lift.BeaconDeposit.LogOnly

/-! # The frozen covered-fork deposit log-shape statement -/

namespace Blanc.Corpus.Proofs.Deposit

open Jaune Blanc Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

/-- Every selected kept-frame log is accepted with its exact 192-byte deposit record.
The entry machine and installed image are derived from the supplied kept history. -/
theorem log_shape : LogShape CoveredFork := by
  intro cfg start stop blocks history forks installed block blockMember frame frameMember
    log logMember
  obtain ⟨original, entry⟩ := history.entry_in installed beaconInstalledCertH.nonempty
    beaconInstalledCertH.notDelegation block blockMember frame frameMember
  have fresh := history.fresh depositAddr block blockMember frame frameMember
  have appended := List.mem_of_mem_filter logMember
  rcases frame with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have zero : pc = 0 := entry.pc
      subst pc
      have forkEq : sevm.benvStat.fork = block.fork := by
        rw [entry.benvStat]
        rfl
      have fork : CoveredFork sevm.benvStat.fork := by
        rw [forkEq]
        exact forks block blockMember
      obtain ⟨ev, event, accepted, length⟩ := successful_log_shape entry.code fork
        entry.dataLength fresh.1 fresh.2 run log appended
      rw [entry.target] at event
      exact ⟨ev, event, accepted, length⟩

end Blanc.Corpus.Proofs.Deposit
