import Blanc.Corpus.Freeze.BeaconRoots
import Blanc.Lift.BeaconRoots.Frame
import Blanc.Lift.BeaconRoots.Read

namespace Blanc.Corpus.Proofs.BeaconRoots

open Jaune Blanc.Lift Blanc.Corpus.Freeze
open Blanc.Lift.BeaconRoots
open Blanc.Corpus.Freeze.BeaconRoots

/-- Both storage charges are determined by the original access set: the keys differ. -/
theorem read_charge (sevm : Sevm) (pre : Devm) :
    sloadCost sevm (afterSload sevm pre (Sevm.dataWord sevm 0 % (0x1fff : B256)))
        ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256)) +
      sloadCost sevm pre (Sevm.dataWord sevm 0 % (0x1fff : B256)) + 120 =
        readGas pre sevm.currentTarget (Sevm.dataWord sevm 0) := by
  have distinct := read_keys_ne (Sevm.dataWord sevm 0)
  unfold readGas sloadGas rootKey timeKey ring
  unfold sloadCost
  rw [afterSload_accessedStorageKeys]
  unfold sloadAccessedStorageKeys
  split
  · omega
  · simp only [Std.HashSet.mem_insert, beq_iff_eq, Prod.mk.injEq, true_and,
      distinct, false_or]
    omega

/-- The frozen guard and 31-byte controls, without a memory or value restriction. -/
theorem r_s2_control : R_S2_control := by
  intro sevm pre post code fork caller stack fails
  rcases fails with ⟨length, guard⟩ | length
  · apply exec_bad_guard code fork stack caller
    by_cases zero : Sevm.dataWord sevm 0 = 0
    · exact Or.inl zero
    · right
      intro tag
      have pass : Sevm.dataWord sevm 0 ≠ 0 ∧
          (Devm.getStor pre sevm.currentTarget).get (timeKey (Sevm.dataWord sevm 0)) = Sevm.dataWord sevm 0 :=
        ⟨zero, tag⟩
      rw [Blanc.Corpus.Freeze.BeaconRoots.read, ite_eq_left pass] at guard
      cases guard
  · exact exec_31_bytes code fork stack caller length

/-- A fresh accepted read executes at exactly the frozen warm/cold charge. -/
theorem r_s7 : R_S7 := by
  intro sevm pre w code fork caller length stack memory accepts gas
  unfold Blanc.Corpus.Freeze.BeaconRoots.read at accepts
  split at accepts
  next guard =>
    have word : readWord sevm pre = w := Option.some.inj accepts
    let G := pre.gasLeft - readGas pre sevm.currentTarget (Sevm.dataWord sevm 0)
    have align : G +
        sloadCost sevm (afterSload sevm pre (Sevm.dataWord sevm 0 % (0x1fff : B256)))
          ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256)) +
        sloadCost sevm pre (Sevm.dataWord sevm 0 % (0x1fff : B256)) + 120 = pre.gasLeft := by
      have charge := read_charge sevm pre
      dsimp only [G]
      omega
    have exec := exec_read_exact G code fork caller length guard.1 guard.2
    rw [align, ← memory, ← St.self stack rfl] at exec
    refine ⟨readPost sevm pre G, exec, ?_, ?_, ?_⟩
    · rfl
    · change ((Mem.empty.write 0 (readWord sevm pre).toBytes).read 0 32).1 = w.toBytes
      rw [← word]
      have back := Mem.read_write_zero Mem.empty (ys := (readWord sevm pre).toBytes) (by
        intro h
        have hn := congrArg List.length h
        simp only [B256.length_toBytes, List.length_nil] at hn
        omega)
      simpa only [B256.length_toBytes] using back
    · change (readBase sevm pre).state = pre.state
      simp only [readBase, RequestFee.afterSload_state]
  next impossible => cases accepts

end Blanc.Corpus.Proofs.BeaconRoots
