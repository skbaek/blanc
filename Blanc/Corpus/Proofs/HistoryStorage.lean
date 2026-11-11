import Blanc.Corpus.Freeze.HistoryStorage
import Blanc.Lift.HistoryStorage.Frame
import Blanc.Lift.HistoryStorage.Read
import Blanc.ExecutionKeptEntered

/-! # Exact frozen H-S2 classification and controls, and H-S7 witness -/

namespace Blanc.Corpus.Proofs.HistoryStorage

open Jaune Blanc Blanc.Corpus.Freeze
open Blanc.Corpus.Freeze.HistoryStorage

/-- Every settled frame in the frozen kept-history scope has exactly one of the bytecode's two effects. -/
theorem h_s2 : H_S2 := by
  intro cfg start stop blocks history covered code f member
  obtain ⟨b, block, frame⟩ := List.mem_flatMap.mp member
  obtain ⟨orig, entry⟩ := history.entry_in code (by decide +kernel) (by decide +kernel) b block f frame
  have empty := history.keptAt_output covered addr b block f frame
  rcases f with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have zero : pc = 0 := entry.pc
    subst pc
    have fork : CoveredFork sevm.benvStat.fork := by
      rw [entry.benvStat]
      exact covered b block
    by_cases caller : sevm.caller = systemAddress
    · left
      obtain ⟨dynamic, state, output, logs⟩ :=
        Blanc.Lift.HistoryStorage.exec_system_frame entry.code fork entry.stack caller run
      exact ⟨caller, dynamic, state, output.trans empty, logs⟩
    · right
      obtain ⟨length, upper, lower, output, state, logs⟩ :=
        Blanc.Lift.HistoryStorage.exec_read_frame entry.code fork entry.stack entry.dataLength caller run
      refine ⟨caller, length, ⟨pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % 8191), ?_, output⟩,
        state, logs⟩
      change (if InWindow sevm.benvStat.number.toB256 (Sevm.dataWord sevm 0) then
        some (pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % 8191)) else none) = _
      exact ite_eq_left ⟨upper, lower⟩

theorem h_s2_control : H_S2_control := by
  intro sevm pre post code fork caller stack fails
  refine ⟨fun exec => ?_⟩
  obtain ⟨length, upper, lower, _⟩ :=
    Blanc.Lift.HistoryStorage.exec_read_path code stack caller exec
  rcases fails with ⟨_, outside⟩ | short
  · exact outside ⟨upper, lower⟩
  · rw [short] at length
    exact (by decide : (Nat.toB256 31 : B256) ≠ 32) length

theorem h_s7 : H_S7 := by
  intro sevm pre code fork caller length stack memory window gas
  have charge : readGas pre sevm.currentTarget (Sevm.dataWord sevm 0) =
      Blanc.sloadCost sevm pre (Sevm.dataWord sevm 0 % 8191) + 125 := by
    unfold readGas sloadGas Blanc.sloadCost ring
    exact Nat.add_comm _ _
  rw [charge] at gas ⊢
  exact Blanc.Lift.HistoryStorage.read_exec code fork caller length stack memory window.1 window.2 gas

end Blanc.Corpus.Proofs.HistoryStorage
