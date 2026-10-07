import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Init
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Deploy

/-! # V− setup, messages 4–5: executed creation of the token and the attacker

From exactly the world `setup_initialize` settles to (the clean, initialized pool), the
code-free `creator` executes two further root CREATE messages, each starting from the previous
settled world, on every covered fork:

* message 4 creates the shared token fixture `T` at `tokenAddr`; its constructor mints
  `balanceOf[creator] := 10^6` and installs the registered `Token20` runtime;
* message 5 creates the reachable attacker at `attackerAddr`; it installs the registered
  `AttackerR` runtime (the EOA-triggerable dispatcher repointed to `attackerAddr` and the new
  proxy).

`setup_funded` composes messages 1–5 and states the reached world `W4`: the token holds
`balanceOf[creator] = 10^6` with the token runtime, the attacker holds the attacker runtime,
the implementation keeps `fee = 31337`, the creator stays funded, and the proxy's storage is
still exactly the initializer's clean `initWrites` (the funding creations touch neither the
pool nor the implementation). This is the executed funding-contract step of V3; the `approve`
and first `add_liquidity` calls (which run node walks over a non-closed settled world, so need
the transaction-original-state agreement transport) continue from here. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
