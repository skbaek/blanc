import Blanc.Corpus.Freeze.HistoryStorage
import Blanc.Lift.HistoryStorage.Frame
import Blanc.Lift.HistoryStorage.Read

/-! # Exact frozen H-S2 controls and H-S7 witness -/

namespace Blanc.Corpus.Proofs.HistoryStorage

open Jaune Blanc Blanc.Corpus.Freeze
open Blanc.Corpus.Freeze.HistoryStorage

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
