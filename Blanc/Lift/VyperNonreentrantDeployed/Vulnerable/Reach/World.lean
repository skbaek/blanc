import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach.World
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Input
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Clone.Input

/-! # The disclosed V− reachable-setup world and its root messages

Modeled addresses and messages for the reachable V− setup sequence. The root-message conventions
are V+'s, reused rather than restated (`Fixed.Reach.createMsg`, `rootBenv`, `rootTenv`): every
root message comes from the code-free `Fixed.Reach.creator`; each message's input world is the
previous settled `post.state`, with that world also as the block-original state (`origState`),
as for a fresh transaction. Message level only: no transaction admission, signature or nonce
derivation.

* `implAddr` is `curvePlainImpl6326`, the address the registered runtime, the forwarder and the
  existing V− witness name. The modeled CREATE supplies it as its target; it is not derived from
  the historical deployer and claims no historical inclusion.
* `proxyAddr` is a fresh modeled address for the synthetic clone (distinct from V+'s
  `0x2222…`); it is not the historical pool `0x9848…85c5`.
* `tokenAddr` is the fixed address the shared token fixture will occupy (master decision: the
  same constant in both lanes). The initializer stores it as `coins[1]` and makes no call to it.
* `initialWorld` is V+'s disclosed starting world: the funded, code-free creator only. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune

export Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv
  rootTenv createMsg)

/-- The implementation's modeled address: the address its runtime is registered under. -/
abbrev implAddr : Adr := Blanc.curvePlainImpl6326

/-- The clone's fresh modeled address (synthetic). -/
def proxyAddr : Adr := 0x5555555555555555555555555555555555555555

/-- The shared token fixture's address (synthetic; coin 1). -/
def tokenAddr : Adr := 0x3333333333333333333333333333333333333333

/-- Message 1: the preserved implementation creation input, 4,000,000 gas. -/
def implCreateMsg (fork : Fork) (W : State) : Msg :=
  createMsg fork W implAddr Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.creationCode
    4000000

/-- Message 2: the **synthetic** clone creation input, 100,000 gas. -/
def cloneCreateMsg (fork : Fork) (W : State) : Msg :=
  createMsg fork W proxyAddr Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Clone.cloneCreationCode
    100000

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
