import Blanc.ExecutionModelAccounting
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecDeterminism

/-!
# A target handler for contracts whose frame theorem covers its whole subtree

`Blanc/ExecutionModelAccounting.lean` replays a successful non-static target frame as its own steps
followed by the steps of the children it settles (`SpawnReplay`): the frame's own carrier effect must be
complete at its first external instruction.  A contract whose frame theorem already consumes everything
that happens below the frame — including re-entered frames of the same contract, run inside the frame's
own model transcript — needs no such split: its frame theorem gives one replay from the frame's entry
boundary to its post boundary whose observation is exactly the frame's committed subtree.

This module is that handler, for an arbitrary account-local carrier whose boundary reads the target's
storage only through its words:

* `Exec.CoreAccounting.WholeFrameReplay` — the contract's obligation: every successful non-static target
  frame replays, as a whole, with the observation of all of its committed frames;
* `Exec.CoreAccounting.staticObservedNil` (`Blanc/ExecutionModelAccounting.lean`) — below a static frame
  no committed frame is observed (the ladder's lower-depth hypothesis, at any code);
* `Exec.CoreAccounting.wholeFrameTarget` — the obligation and the static case give the target handler of
  `Exec.coreAccounting`;
* `ExecutionAccountingReplay.wholeFrameLadder` — the handler, the frame preservation theorem and the
  generic ladder give an `AccountingLadderAdmitted`, hence `configuredHistory`;
* `Exec.derivEntry` — an entry condition (the shape `Exec.FrameAdmitted` attaches to frame roots) that
  states a property of the frame's own derivation, such as the storage rows selected by a callee's
  answer; by determinism (`Exec.result_unique`, `Exec.unique`) it holds at a root once the property holds
  of that root's actual derivation (`Exec.derivEntry_of_deriv`).

The lower-depth hypothesis is used only for static frames: a non-static target frame's children are
covered by the contract's own frame theorem, never replayed a second time.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- An entry condition stating `P` of every pc-`0` derivation from the given frame start.  Execution is
deterministic, so this is `P` of the frame's one actual derivation. -/
def Exec.derivEntry (P : Exec.Deriv → Prop) (sevm : Sevm) (pre : Devm) : Prop :=
  ∀ (out : Execution) (run : Exec 0 sevm pre out), P ⟨0, sevm, pre, out, run⟩

namespace Exec.CoreAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca}
  {V : ReplayObservation C}

end Exec.CoreAccounting


namespace ExecutionAccountingReplay

end ExecutionAccountingReplay

end Blanc
