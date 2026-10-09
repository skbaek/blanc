import Blanc.Lift.UniswapV2Pair.MutableTurns

/-!
# World effects of a mutable external call, tied to its turns

`mutable_call_turns` derives the turn queue of one actual CALL/STATICCALL step and says, in a
separate existential, which child produced the turns. This module restates that consumption
with the child pinned to the step itself (`Xinst.Run` of the same pre-state and post-state)
and adds what the child derivation gives for the storage of every code-bearing account after
the call: the committed child's endpoint storage when the turns come from a committed child,
and the pre-call storage when the call produced no turn (no frame was entered, or the entered
child rolled back). The swap frame consumes it for its two optimistic transfers and its
callback.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The provenance of one actual mutable call step `pre → d` of derivation `D` with turn
queue `turns`: either no turn, no committed child and every code-bearing account's storage
as before the call; or one committed child of this very step, a sub-derivation of `D`, whose
retained Pair events are the turns and whose committed endpoint is every code-bearing
account's storage after the call. -/
def MutableCallWorld (pair : Adr) (D : Exec.Deriv) (sevm : Sevm) (pre : Devm) (x : Xinst)
    (d : Devm) (turns : List MutableTurn) : Prop :=
  (turns = [] ∧
    (Xinst.Run sevm pre x .none (.ok d) ∨ ∃ (child : Evm) (raw : Execution),
      Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok d) ∧ ¬ Execution.commits raw = true) ∧
    ∀ a, pre.getCode a ≠ .empty → ∀ key, (d.getStor a).get key = (pre.getStor a).get key) ∨
  ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw)
    (committed : Execution.commits raw = true),
    Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok d) ∧
    (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
    turns.map MutableTurn.event = Exec.targetLogEventsFrom pair [] 0 childRun committed ∧
    ∀ a, pre.getCode a ≠ .empty → ∀ key,
      (d.getStor a).get key = ((Execution.committedPost raw committed).getStor a).get key

end Blanc.Lift.UniswapV2Pair
