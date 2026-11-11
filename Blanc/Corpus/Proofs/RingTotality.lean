import Blanc.Lift.BeaconRoots.Totality
import Blanc.Lift.HistoryStorage.Totality
import Blanc.SystemCallEmpty
import Blanc.Corpus.Freeze.BeaconRoots
import Blanc.Corpus.Freeze.HistoryStorage
import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk
import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk

namespace Blanc.Corpus.Proofs
open Jaune Blanc Blanc.Lift
open Blanc.Corpus.Freeze
open Blanc.Lift.RequestSystem (RegularGasWithin)

namespace R
open Blanc.Corpus.Freeze.BeaconRoots
open Blanc.Lift.SystemExecution.BeaconRoots

private theorem value_eq (benv : Benv) : systemValue benv = benv.stat.parentBeaconBlockRoot := by
  apply dataWord_of_append (pre := []) (post := []) rfl
  simp only [systemSevm, systemMsg, systemCallMsg, List.nil_append, List.append_nil]
  rfl

theorem r_s1 : R_S1 := by
  intro benv fork installed
  have h := processUncheckedSystemTransaction_beaconRoots fork installed
  have hs : (systemPost benv).state = writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot := by
    rw [h.2.1, value_eq]
    rfl
  refine ⟨systemCallOutput (systemPost benv), ?_, ?_, ?_, ?_⟩
  · rw [← hs]; exact h.1
  · have c1 := sstoreCost_le (systemSevm benv) (systemBase benv) (systemKey benv) (systemSevm benv).benvStat.time
    have c2 := sstoreCost_le (systemSevm benv) (systemMid benv) (systemRootKey benv) (systemValue benv)
    simp only [gasColdSload, gasStorageSet] at c1 c2
    change (systemTransactionGas - (52 + systemCost benv) + 1 ≤ systemTransactionGas) ∧ _
    change (30000000 - (52 + _) + 1 ≤ 30000000) ∧ (30000000 - (30000000 - (52 + _) + 1) ≤ 44251)
    simp only [systemCost] at *
    omega
  · change (afterSstore (systemSevm benv) (systemMid benv) (systemRootKey benv) (systemValue benv)).output = []
    rw [afterSstore_output, systemMid, afterSstore_output]
    rfl
  · have enabled : benv.stat.rules.sys.beaconRoots = true := by
      have hf := fork
      simp only [CoveredFork, coveredForks, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with hf | hf | hf | hf <;> simp only [BenvStat.rules, hf] <;> rfl
    unfold beaconRootsCall
    rw [enabled, h.1, hs]
    exact ⟨_, rfl⟩
/-- The empty-code control changes only the installed-code premise. -/
theorem r_s1_control : R_S1_control := by
  intro benv fork empty differs
  obtain ⟨out, call⟩ := processUncheckedSystemTransaction_empty (data := benv.stat.parentBeaconBlockRoot.toBytes)
    fork empty (systemContracts_not_precompile member fork)
  refine ⟨benv.state, out, call, ?_⟩
  intro same
  apply differs
  have sameSlot := congrArg (fun w => storOf w addr (timeKey benv.stat.time)) same
  have different : rootKey benv.stat.time ≠ timeKey benv.stat.time := (systemKey_ne benv).symm
  simpa only [writeState, storOf, State.getStor_setStorVal_self, Stor.get_set_ne _ different,
    Stor.get_set_self] using sameSlot
/-- The frozen protocol-call statement under Amsterdam's regular and state gas rules. -/
theorem r_s10 : R_S10 := by
  intro benv fork installed
  obtain ⟨out, call, gas⟩ := Blanc.Lift.BeaconRoots.Totality.call_ok fork installed
  have hs : (benv.state.setStorVal beaconRootsAddress (systemKey benv) benv.stat.time).setStorVal
      beaconRootsAddress (systemRootKey benv) (systemValue benv) =
      writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot := by
    rw [value_eq]
    rfl
  rw [hs] at call
  refine ⟨out, call, gas, ?_⟩
  have enabled : benv.stat.rules.sys.beaconRoots = true := by rw [amsterdam_rules fork]; rfl
  unfold beaconRootsCall
  rw [enabled, call]
  exact ⟨_, rfl⟩
end R

namespace H
open Blanc.Corpus.Freeze.HistoryStorage
open Blanc.Lift.SystemExecution.HistoryStorage
private theorem value_eq (benv : Benv) : systemValue benv = benv.stat.blockHashes.getLast?.getD 0 := by
  apply dataWord_of_append (pre := []) (post := []) rfl
  simp only [systemSevm, systemMsg, systemCallMsg, List.nil_append, List.append_nil]
  rfl

theorem h_s1 : H_S1 := by
  intro benv bal lastHash fork installed last
  have h := processUncheckedSystemTransaction_historyStorage fork installed last
  have hs : (systemPost benv).state = benv.state.setStorVal addr (key benv.stat.number.toB256) lastHash := by
    rw [h.2.1, value_eq, last]
    rfl
  refine ⟨systemCallOutput (systemPost benv), ?_, ?_, ?_, ?_⟩
  · rw [← hs]; exact h.1
  · have c := sstoreCost_le (systemSevm benv) (systemBase benv) (systemKey benv) (systemValue benv)
    simp only [gasColdSload, gasStorageSet] at c
    change (systemTransactionGas - (43 + systemCost benv) ≤ systemTransactionGas) ∧ _
    change (30000000 - (43 + _) ≤ 30000000) ∧ (30000000 - (30000000 - (43 + _)) ≤ 22143)
    simp only [systemCost] at *
    omega
  · change (afterSstore (systemSevm benv) (systemBase benv) (systemKey benv) (systemValue benv)).output = []
    rw [afterSstore_output]
    rfl
  · have enabled : benv.stat.rules.sys.historyStorage = true := by
      have hf := fork
      simp only [CoveredFork, coveredForks, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with hf | hf | hf | hf <;> simp only [BenvStat.rules, hf] <;> rfl
    unfold historyStorageCall
    rw [enabled, last]
    simp only [Option.toExcept, bind, Except.bind]
    rw [h.1, hs]
    exact ⟨_, rfl⟩
/-- The empty-code control changes only the installed-code premise. -/
theorem h_s1_control : H_S1_control := by
  intro benv lastHash fork empty _last differs
  obtain ⟨out, call⟩ := processUncheckedSystemTransaction_empty (data := lastHash.toBytes)
    fork empty (systemContracts_not_precompile member fork)
  refine ⟨benv.state, out, call, ?_⟩
  intro same
  apply differs
  have sameSlot := congrArg (fun w => storOf w addr (key benv.stat.number.toB256)) same
  simpa only [storOf, State.getStor_setStorVal_self, Stor.get_set_self] using sameSlot
/-- The frozen history-call statement under Amsterdam's regular and state gas rules. -/
theorem h_s10 : H_S10 := by
  intro benv bal lastHash fork installed last
  obtain ⟨out, call, gas⟩ := Blanc.Lift.HistoryStorage.Totality.call_ok fork installed
  have hv : systemValue benv = lastHash := by rw [value_eq, last]; rfl
  have hk : systemKey benv = key benv.stat.number.toB256 := rfl
  simp only [last, Option.getD_some, hv, hk] at call
  refine ⟨out, call, gas, ?_⟩
  have enabled : benv.stat.rules.sys.historyStorage = true := by rw [amsterdam_rules fork]; rfl
  unfold historyStorageCall
  rw [enabled, last]
  simp only [Option.toExcept, bind, Except.bind]
  rw [call]
  exact ⟨_, rfl⟩
end H
end Blanc.Corpus.Proofs
