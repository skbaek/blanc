import Blanc.Corpus.Freeze.DepositCells
import Blanc.ExecutionKeptFresh
import Blanc.Lift.BeaconDeposit.LogOnly

/-! # The frozen kept-fork deposit log-shape statement -/

namespace Blanc.Corpus.Proofs.Deposit

open Jaune Blanc Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

/-- Every selected kept-frame log is accepted with its exact 192-byte deposit record.
The entry machine and installed image are derived from the supplied kept history. -/
theorem log_shape_kept : LogShape KeptFork := by
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
      have fork : KeptFork sevm.benvStat.fork := by
        rw [forkEq]
        exact forks block blockMember
      obtain ⟨ev, event, accepted, length⟩ := successful_log_shape_kept_any_data entry.code fork
        fresh.1 fresh.2 run log appended
      rw [entry.target] at event
      exact ⟨ev, event, accepted, length⟩

/-- Original covered-domain compatibility projection of the same kept-history proof. -/
theorem log_shape : LogShape CoveredFork := by
  intro cfg start stop blocks history forks installed
  exact log_shape_kept history (fun block member => Or.inl (forks block member)) installed

/-- Literal frozen Amsterdam log-shape statement over the supplied actual kept history. -/
theorem log_shape_amsterdam : LogShape (fun fork => fork = .amsterdam) := by
  intro cfg start stop blocks history forks installed
  exact log_shape_kept history (fun block member => Or.inr (forks block member)) installed

end Blanc.Corpus.Proofs.Deposit
