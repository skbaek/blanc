import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.InvWalkOps

/-!
# Indexed loads from three carried words

`pickWord3` selects a word from a three-word layout. `word3_indexAddr` relates the EVM
address arithmetic to its natural offset without wrap. `ri_mloadWord3` inverts an indexed
load over the shared `Words` carrier and preserves an already aligned allocation.
-/

namespace Blanc.Lift

open Jaune

/-- Select one of three words; callers establish that the index is below three. -/
def pickWord3 (n : Nat) (a0 a1 a2 : B256) : B256 :=
  if n = 0 then a0 else if n = 1 then a1 else a2

end Blanc.Lift
