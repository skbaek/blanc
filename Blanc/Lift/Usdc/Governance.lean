import Blanc.Lift.Token.Core
import Blanc.Lift.Usdc.Constants

/-!
# The USDC governance premise F2 (decision usdc-governance-f2)

The proxy's admin may replace the implementation (`upgradeTo`, `upgradeToAndCall`) or hand over the
admin word (`changeAdmin`).  F2 is the trace-local environment premise that the checkpoint's admin
word calls none of these three entry points at the proxy in the history.  It names an actor and
three entry points, and no outcome.  `UsdcInstalled` and `UsdcHist` need U3's certified semantics and
live with the history theorems.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.Token

/-- **The governance premise F2** (ENV, trace-local; decision usdc-governance-f2): no settled entry
frame at the proxy whose caller is the checkpoint's admin word and whose selector is `upgradeTo`,
`upgradeToAndCall` or `changeAdmin`.  It names an actor and three entry points, no outcome. -/
def UsdcGovernance {cfg : ChainConfig} {checkpoint future : BlockChain} (P : Adr)
    (tr : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ G ∈ tr.settledFrames, IsEntry P G → G.sevm.caller = adminOf checkpoint.state P →
    Blanc.Sevm.selector G.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970]

end Blanc.Lift.Usdc
