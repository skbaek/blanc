import Blanc.Composition.UniswapV2PairWeth9W0
import Blanc.Lift.Weth9.ClosedDeployment

/-!
# `W0`'s touched storage words (kernel evaluation)

The four storage words the closed instance's two transactions read from `W0`'s token storages:
`X`'s balances of the trader (`100000`) and of the Pair (`10^6`), WETH9's balances of the Pair
(`10^6`) and of the trader (`0`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

theorem w0TokenStor_trader :
    w0TokenStor.get (VyperNonreentrantDeployed.Token20.balSlot trader) = 100000 := by
  decide +kernel

theorem w0TokenStor_pair :
    w0TokenStor.get (VyperNonreentrantDeployed.Token20.balSlot pair) = 1000000 := by
  decide +kernel

theorem w0WethStor_pair : w0WethStor.get (Weth9.balSlot pair) = 1000000 := by
  decide +kernel

theorem w0WethStor_trader : w0WethStor.get (Weth9.balSlot trader) = 0 := by
  decide +kernel

theorem systemWorld_code (a : Adr) (ha : a ∈ Weth9.ClosedInstance.systemAddresses) :
    (Weth9.ClosedInstance.systemWorld.get a).code = Weth9.ClosedInstance.systemCode := by
  revert a
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Instance
