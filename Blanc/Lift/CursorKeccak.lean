import Blanc.Lift.ReachSstoreLoops
import Blanc.Lift.CursorOccurrence

/-! Successful observed hashes at their original raw-prefix positions. -/

namespace Blanc.Lift

open Jaune

/-- One actual successful hash, with its exact input and ordered edge before the given stop. -/
def KeccakBefore (root stop : Exec.Deriv) (input : Bytes) (pc : Nat) : Prop :=
  ∃ (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
    occurrence.node.pc = pc ∧ occurrence.instruction = .reg .keccak256 ∧
    occurrence.stepResult = .ok next.devm ∧
    Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
    Exec.Deriv.ParentPrefix next stop ∧
    (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
    (occurrence.node.devm.memory.read 0 64).1 = input

end Blanc.Lift
