import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute

/-!
# Triggerable Withdrawals Gateway: pause/query Phase-A surface

This module records the exact public-runtime route and the source projections
used by the pause/query rows.  The route theorem below starts from
`Prog.RunCompiledTo`, uses the runtime guard and selector inversion from
`dispatcher_body_of_prog_run`, and specializes the selected body to the
family's pause/query functions.  Storage effects are stated at the exact
`SSTORE` instruction boundary; the remaining work is to compose those
instruction boundaries through the ABI/role branches into public postconditions.
No evaluator, `Nonempty`, sibling-family import, or assumed dispatcher walk is
used.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway


/-! ## Exact public selector routes -/

/-! ## Exact instruction-level storage boundary -/

end LidoTriggerableWithdrawalsGateway
end Blanc
