import Blanc.Lift.WitnessChild

/-!
Frame-level spawn facts for witness runs: a machine is *spawned by* a parent machine
executing a call-family instruction when that instruction's step spawns a frame which enters
as the machine.  These lemmas read the fact off the witness engine's shadow computations
(`callPrep`, `dcallPrep`, `childStart`), so a statement about a nested execution can name
each frame's entry machine and its parent in Jaune's own terms (`Xinst.step`,
`Frame.enter`).  Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-- `child` is the machine of a frame that the parent machine `⟨sevm, devm⟩` spawns by
executing the call-family instruction `x`: the step spawns a frame, and that frame enters
(Jaune's `Frame.enter`, value transfer included) as `child`. -/
def SpawnedBy (sevm : Sevm) (devm : Devm) (x : Xinst) (child : Evm) : Prop :=
  ∃ f rsm, Xinst.step sevm devm x = .spawn f rsm ∧ f.enter = .run child

end Blanc.Lift.Witness
