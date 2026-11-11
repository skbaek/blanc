import Blanc.Corpus.Proofs.BeaconRootsFrames
import Blanc.ExecutionKeptEntered

namespace Blanc.Corpus.Proofs.BeaconRoots

open Jaune Blanc.Lift Blanc.Corpus.Freeze
open Blanc.Lift.BeaconRoots
open Blanc.Corpus.Freeze.BeaconRoots

/-- Every settled frame in the frozen kept-history scope has exactly one of the bytecode's two effects. -/
theorem r_s2 : R_S2 := by
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
      obtain ⟨dynamic, state, output, logs⟩ := exec_system entry.code fork entry.stack caller run
      exact ⟨caller, dynamic, state, output.trans empty, logs⟩
    · right
      obtain ⟨length, nonzero, tag, output, state, logs⟩ := exec_read entry.code fork entry.stack caller run
      have literal : sevm.data.length = 32 := by
        have values := congrArg B256.toNat length
        rwa [B256.toNat_toB256_of_lt entry.dataLength] at values
      refine ⟨caller, literal, ⟨readWord sevm pre, ?_, output⟩, state, logs⟩
      change (if Sevm.dataWord sevm 0 ≠ 0 ∧
        pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) = Sevm.dataWord sevm 0 then
          some (readWord sevm pre) else none) = some (readWord sevm pre)
      exact ite_eq_left ⟨nonzero, tag⟩

end Blanc.Corpus.Proofs.BeaconRoots
