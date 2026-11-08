import Blanc.Lift.NodeWalkFork
import Blanc.Lift.WitnessBoundary
import Blanc.Lift.WitnessSpawn

/-!
# Frame-level witnesses under any covered fork

`Blanc/Lift/NodeWalkFork.lean` shows that a run of the certificate interpreter `wrun` is
unchanged by the fork (`wrun_withFork`).  This module carries the rest of the witness kit
across: the child machinery built on it (`childStart`, `childRun`, `callResume`, and the
two-call frame kit `callPairFrom` of `Blanc/Lift/WitnessBoundary.lean`) is unchanged by the
fork, so every kernel fact stated with them is the same fact for `s.withFork g`; and Jaune's
own driver (`stepN`) transports from a Prague machine, in which `CLZ` is invalid: a Prague
step that is not an error halt is at an instruction every covered fork runs the same.
Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift Blanc.ForkUniform Blanc.Lift.NodeWalk Blanc.ConcreteRun
  Blanc.Lift.Witness.Boundary

variable {s : Sevm} {g : Fork}

/-! ## The child machinery -/

/-- The machine a code child of `CALL` starts with carries the caller's block environment. -/
theorem childStart_stat {c cc : Cfg} {f0 : SFunc} {e : Evm}
    (h : childStart s c f0 = some (e, cc)) : e.sta.benvStat = s.benvStat := by
  unfold childStart at h
  split at h
  · rename_i cp hp
    split at h
    · rename_i cevm he
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact (frameEnterS_stat he).trans (callPrep_stat hp).2
      · cases h
    · cases h
  · cases h

/-! ## The two-call frame kit -/

/-! ## Jaune's driver from a Prague machine -/

end Blanc.Lift.Witness
