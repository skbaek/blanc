import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary

/-!
# V− V4, the re-entrant `add_liquidity` frame (F5): steps 0 to 1159

Prague kernel decisions of the re-entrant frame's run (static machine `sRe`, original state
`O0`, certificate interpreter `fsI`) between the committed literal boundaries of
`ViolBoundary.lean`, over **free** shadow tails, world and bookkeeping
(`Boundary.cfgOfT`/`obsDT`, `Blanc/Lift/ShadowTail.lean`): the literal prefixes are decided,
the tails compared as terms.  Do not open this file in the language server.

* `reChunk1112`: entry `bRe0` to step 1112 (`bRe1112`, node `t_0185_c2`);
* `reChunk1159`: step 1112 to step 1159 (`bRe1159`, node `t_0158_c45`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- Steps 0 to 1112, over any tails, world and bookkeeping. -/
theorem reChunk1112 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe1112 (wrun fsI sRe 1112 (Boundary.cfgOfT bRe0 tS tA m w)) =
      Boundary.obsDOkT bRe1112 tS tA := by
  kernel_forall_rfl

/-- Steps 1112 to 1159, over any tails, world and bookkeeping. -/
theorem reChunk1159 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe1159 (wrun fsI sRe 47 (Boundary.cfgOfT bRe1112 tS tA m w)) =
      Boundary.obsDOkT bRe1159 tS tA := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
