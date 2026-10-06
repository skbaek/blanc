import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary

/-!
# V− V4, the re-entrant `add_liquidity` frame (F5): steps 1159 to 2625

Prague kernel decisions of the re-entrant frame's run (static machine `sRe`, original state
`O0`) between the committed literal boundaries, over free shadow tails, world and
bookkeeping (as `ViolReRun1.lean`).  Do not open this file in the language server.

* `reChunk2527`: step 1159 (`bRe1159`) to step 2527 (`bRe2527`, node `t_02c4_c46`): 1,368
  steps, no boundary between them at a named node with no pending return;
* `reChunkBody`: step 2527 to step 2625 (`bReBody`, node `t_0370_c63`): `add_liquidity`'s
  body past its guard, lock slot 0 taken while lock slot 2 is held.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- Steps 1159 to 2527, over any tails, world and bookkeeping. -/
theorem reChunk2527 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe2527 (wrun fsI sRe 1368 (Boundary.cfgOfT bRe1159 tS tA m w)) =
      Boundary.obsDOkT bRe2527 tS tA := by
  kernel_forall_rfl

/-- Steps 2527 to 2625 (`add_liquidity`'s body), over any tails, world and bookkeeping. -/
theorem reChunkBody : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bReBody (wrun fsI sRe 98 (Boundary.cfgOfT bRe2527 tS tA m w)) =
      Boundary.obsDOkT bReBody tS tA := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
