import Blanc.OwnerDiscipline
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.Input
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone.Input

/-! # The disclosed V+ reachable-setup world and its root messages

Modeled addresses and messages for the reachable V+ setup sequence. Every root message comes
from the code-free creator `creator`; each message's input world is the previous settled
`post.state`, with that world also as the block-original state (`origState`), as for a fresh
transaction. Message level only: no transaction admission, signature or nonce derivation.

* `implAddr` is `curvePlainImpl847e`, the address the registered runtime, the forwarder and the
  universal exclusion theorem name. The modeled CREATE supplies it as its target; it is not
  derived from the historical deployer and claims no historical inclusion.
* `proxyAddr` is a fresh modeled address for the synthetic clone; it is not a historical pool.
* `initialWorld` is the disclosed starting world: the funded creator only. Later setup
  fixtures may extend any world satisfying the creation premises (`implAddr`, `proxyAddr`
  absent) without re-proving the creations. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

open Jaune

/-- The code-free root caller (synthetic). -/
def creator : Adr := 0x1111111111111111111111111111111111111111

/-- The implementation's modeled address: the address its runtime is registered under. -/
abbrev implAddr : Adr := Blanc.curvePlainImpl847e

/-- The clone's fresh modeled address (synthetic). -/
def proxyAddr : Adr := 0x2222222222222222222222222222222222222222

/-- The creator's disclosed starting balance: 10^18 wei. -/
def creatorFunds : B256 := 1000000000000000000

/-- The disclosed starting world: only the funded, code-free creator. -/
def initialWorld : State :=
  State.set Std.TreeMap.empty creator { Acct.nil with bal := creatorFunds }

/-- The block environment of a root message over world `W` on `fork`. -/
def rootBenv (fork : Fork) (W : State) : Benv where
  state := W
  createdAccounts := .emptyWithCapacity
  stat := { (default : BenvStat) with fork := fork, origState := W }

/-- The transaction environment of a root message from `creator`. -/
def rootTenv : Tenv :=
  { (default : Tenv) with stat := { (default : TenvStat) with origin := creator } }

/-- A zero-value root CREATE from `creator` over world `W`. -/
def createMsg (fork : Fork) (W : State) (target : Adr) (code : ByteArray) (gas : Nat) : Msg where
  benv := rootBenv fork W
  tenv := rootTenv
  caller := creator
  target := none
  currentTarget := target
  gas := gas
  value := 0
  data := []
  codeAddress := none
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- Message 1: the preserved implementation creation input, 4,000,000 gas. -/
def implCreateMsg (fork : Fork) (W : State) : Msg :=
  createMsg fork W implAddr Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.creationCode
    4000000

/-- Message 2: the **synthetic** clone creation input, 100,000 gas. -/
def cloneCreateMsg (fork : Fork) (W : State) : Msg :=
  createMsg fork W proxyAddr Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone.cloneCreationCode
    100000

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach
