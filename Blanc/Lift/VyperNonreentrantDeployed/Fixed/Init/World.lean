import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach.Exact
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.Setup
import Blanc.Lift.NodeWalkPrecomp
import Blanc.Lift.ShadowCanon

/-! # The V+ setup root calls through the clone

Messages 3 and 4 of the reachable V+ setup are ordinary root calls from the code-free `creator`
to the clone `proxyAddr` (the forwarder `DELEGATECALL`s the implementation, which runs in the
clone's storage):

* `initMsg`: `initialize("", "", [0xEeee…EEeE, T, 0, 0], [10^18, 10^18, 0, 0], 1, 0)` with the
  token address fixed as `tokenAddr = 0x3333…3333`, value 0, 1,000,000 gas;
* `oracleMsg`: `set_oracle(0x00000000, 0x0)`, value 0, 100,000 gas.

Root-call conventions, disclosed (`callBenv`, `callMsg`): the block environment is
`Reach.rootBenv` (the input world as `origState`, a fresh transaction) with chain id
`chainIdV2 = 1` and timestamp `timeV2 = 1700000000`; the transaction origin is `creator`; the
message is entered at Jaune's root depth 1024 with empty accessed sets and precompiles enabled.
Message level only: no transaction admission, signature, nonce, intrinsic gas or access list.

`WorldIs W acs stor` describes a world by the walk engine's shadows at every address
(`AcctAgree`, storage at every key).  Each message's input world is a closed term (the
creations' `setupState initialWorld`, then the previous call's settled machine), which the
kernel evaluates only where Jaune reads the block-original state: the `SSTORE` charge. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

/-- The disclosed chain id of the setup calls. -/
def chainIdV2 : UInt64 := 1

/-- The disclosed block timestamp of the setup calls (2023-11-14 22:13:20 UTC). -/
def timeV2 : B256 := (1700000000 : Nat).toB256

/-- The pool's token coin (synthetic; it need not have code: neither call reaches it). -/
def tokenAddr : Adr := 0x3333333333333333333333333333333333333333

/-- Vyper's ETH sentinel `0xEeee…EEeE`, the pool's coin 0. -/
def ethSentinel : Nat := 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE

/-- The block environment of a setup root call over world `W`: `rootBenv` with the disclosed
chain id and timestamp; `W` is the original state. -/
def callBenv (fork : Fork) (W : State) : Benv :=
  { rootBenv fork W with
    stat := { (rootBenv fork W).stat with chainId := chainIdV2, time := timeV2 } }

/-- A zero-value root call from `creator` to the clone over world `W`. -/
def callMsg (fork : Fork) (W : State) (data : Bytes) (gas : Nat) : Msg where
  benv := callBenv fork W
  tenv := rootTenv
  caller := creator
  target := some proxyAddr
  currentTarget := proxyAddr
  gas := gas
  value := 0
  data := data
  codeAddress := some proxyAddr
  code := Blanc.forwarderCode Blanc.curvePlainImpl847e
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- The ABI encoding of an empty `string`: its length word 0 (no data words). -/
def emptyStringArg : Bytes := Witness.word 0

/-- `initialize(string,string,address[4],uint256[4],uint256,uint256)` = `0xa461b3c8` with
`("", "", [0xEeee…EEeE, T, 0, 0], [10^18, 10^18, 0, 0], 1, 0)`: twelve head words (the two
string offsets 0x180 and 0x1a0), then the two empty strings. -/
def initCall : Bytes :=
  [0xa4, 0x61, 0xb3, 0xc8] ++ Witness.word 0x180 ++ Witness.word 0x1a0 ++
    Witness.word ethSentinel ++ Witness.word tokenAddr.toNat ++ Witness.word 0 ++
    Witness.word 0 ++ Witness.word 1000000000000000000 ++ Witness.word 1000000000000000000 ++
    Witness.word 0 ++ Witness.word 0 ++ Witness.word 1 ++ Witness.word 0 ++ emptyStringArg ++
    emptyStringArg

/-- `set_oracle(bytes4,address)` = `0xd1d24d49` with `(0x00000000, 0x0)`. -/
def oracleCall : Bytes := [0xd1, 0xd2, 0x4d, 0x49] ++ Witness.word 0 ++ Witness.word 0

/-- **Message 3**: `initialize` through the clone, 1,000,000 gas. -/
def initMsg (fork : Fork) (W : State) : Msg := callMsg fork W initCall 1000000

/-- **Message 4**: `set_oracle(0, 0)` through the clone, 100,000 gas. -/
def oracleMsg (fork : Fork) (W : State) : Msg := callMsg fork W oracleCall 100000

/-! ## Worlds described by shadows -/

/-- The world `W` is described at every address by the account shadow `acs` and the storage
shadow `stor`. -/
def WorldIs (W : State) (acs : AcctShadow) (stor : StorShadow) : Prop :=
  AcctAgree W acs ∧ ∀ a k, storOf W a k = lookupS stor a k

/-- The actual message is the Prague one with its fork changed. -/
theorem callMsg_withFork (fork : Fork) (W : State) (data : Bytes) (gas : Nat) :
    callMsg fork W data gas = (callMsg .prague W data gas).withFork fork := rfl

/-- The world the creations settle to from the disclosed start (`setup_creations_exact`). -/
def world2 : State := setupState initialWorld

/-- The forwarder's code tries (shared with the committing witness). -/
abbrev fwdTries : CodeTries (Blanc.forwarderCode Blanc.curvePlainImpl847e) 6 := Witness2.fwdTries

/-- The funded, code-free creator's account. -/
def creatorAccount : Acct := { Acct.nil with bal := creatorFunds }

/-- The accounts of the world the creations leave (`Reach.setup_creations_initial`). -/
def accts0 : List (Adr × Acct) :=
  [(implAddr, implAccount), (proxyAddr, proxyAccount), (creator, creatorAccount)]

/-- Their account shadow. -/
def acs0 : AcctShadow := acctShadowOf accts0

/-- The storage the creations leave: the implementation's `factory := 1`. -/
def stor0 : StorShadow := [((implAddr, 1), 1)]

/-! ## Projections of walk results (defaults off the run) -/

/-- A walk configuration or a default. -/
def cfgOr (d : PCfg) : PRes → PCfg
  | .cont c => c
  | _ => d

/-- The halted machine of a walk result (a default for a walk that did not halt). -/
def haltOf : PRes → Devm
  | .halt (.ok d) => d
  | .halt (.error (_, d)) => d
  | _ => default

/-- No pc check. -/
def okAny : Nat → Bool := fun _ => true

/-- The prepared call of a `.some` preparation, or a default. -/
def prepOr : Option CallPrep → CallPrep
  | some cp => cp
  | none => ⟨Frame.ofCall (callMsg .prague default [] 0), default, 0, 0, []⟩

/-- The entry machine of a frame entry, or a default. -/
def runOr : FrameEntry → Evm
  | .run e => e
  | .done _ => default

/-- The parent's machine after a call child settled to `d`. -/
def resumeOr (cp : CallPrep) (d : Devm) : Devm :=
  (resumeCallB cp.p cp.oi cp.os (.ok d)).getD default

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
