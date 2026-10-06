import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReAdd
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemove
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolTop

/-!
# V−: the reachable ledger violation

The three headline results of the reachable V− witness, each composed from the frame theorems
against the frozen statements of `ViolBoundary`:

* `vminus_reach_violation : ViolationStmt` — for every covered fork and every world agreeing with
  `Checkpoint`'s finite read set, the violating message settles with `totalSupply = 1800 < 1906 =
  balanceOf[attacker]`, and the same execution's frames show the cross-function reentry;
* `vminus_reachable_capstone : CapstoneStmt` — eight root messages from the disclosed initial world,
  each from the previous settled world: implementation and clone creation, `initialize`, token and
  attacker creation, `approve`, `add_liquidity` (reaching the sound LP ledger), then the violation;
* `vminus_reach_instance : InstanceStmt` — the violation at the closed checkpoint world `worldR`.

Frames: F5 `reAdd_frame` (re-entrant `add_liquidity`), F3/F4 `callback_frame`, F2 `remove_frame`,
F0/F1 `root_frame`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

/-- **The universal reachable V− violation.** -/
theorem vminus_reach_violation : ViolationStmt :=
  root_frame (remove_frame (callback_frame reAdd_frame))

/-- **The reachable V− capstone**: deployment, initialization and liquidity, then the violation. -/
theorem vminus_reachable_capstone : CapstoneStmt :=
  capstone_of_violation vminus_reach_violation

/-- **The standalone V− instance** at the closed checkpoint world. -/
theorem vminus_reach_instance : InstanceStmt :=
  instance_of_violation vminus_reach_violation

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
