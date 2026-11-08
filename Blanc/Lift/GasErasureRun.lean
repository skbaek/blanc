import Blanc.GasErasure
import Blanc.Lift.Silent
import Blanc.ForwardCall

/-!
# Gas erasure over a lifted run

Contract-neutral.  `Blanc/GasErasure.lean` replays two successful runs of one gas-free instruction
or line against each other modulo `gasLeft`.  This module extends that to whole synthetic runs:

* `Ninst.gasFreeRun` widens the instruction whitelist by `KECCAK256` and `LOG n` (their successful
  effects read memory and pay for it, but never read `gasLeft`), with `Ninst.run_eqModGasRun`;
* `Linst.run_eqModGas`: two successful runs of `STOP` or `RETURN` agree modulo gas;
* `SFunc.gasFree` / `GasFreeSet`: a kernel-checkable certificate that a tree and every entry it can
  reach contain only such instructions (no `PC`, no external instruction, no `SELFDESTRUCT`);
* `SFunc.RunP.eqModGas`: two successful runs of a certified tree from states equal modulo gas end
  the same way (both halt or both return) in states equal modulo gas.

The consumer pattern: an arbitrary successful frame and a constructed gas-exact run of the same code
from the same state with more gas have the same output, storage, logs and every other column but
`gasLeft`, so a forward walk's output facts transfer to the actual frame without a gas premise.
-/

namespace Blanc

open Jaune

/-! ## Agreement under the remaining updates -/

theorem Devm.EqModGas.withGasLeft (a : Devm) (g : Nat) : EqModGas a (a.withGasLeft g) :=
  ⟨rfl, rfl, trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

theorem Devm.EqModGas.output_eq {a b : Devm} (h : EqModGas a b) : a.output = b.output := h.output

/-! ## `KECCAK256` and `LOG n` -/

/-! ## The widened whitelist -/

/-! ## Terminals -/

/-! ## Gas-independent forward cost helpers -/

end Blanc

namespace Blanc.Lift

open Jaune Blanc

/-! ## The tree certificate -/

end Blanc.Lift
