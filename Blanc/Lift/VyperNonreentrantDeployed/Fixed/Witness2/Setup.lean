import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.Setup
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Receiver.Cert
import Blanc.Lift.KernelBatch

/-!
# V+ committing witness: the pre-state and the top-level message

The explicit Prague pre-state of the committing V+ witness (synthetic; scenario disclosed in
`Witness2/Top.lean`):

* the ETH/stETH pool `P = curveStethPool847e` (`0x21e2…843a`) holds the 45-byte EIP-1167
  forwarder to the comparator `I = 0x847e…ed9`, 1000 wei, and the storage lock (slot 0) = 3
  (released), `coins[1]` (slot 3) = `X`, `totalSupply` (slot 0x16) = 1000 and the liquidity
  balance of the caller `S`;
* `I` holds the deployed 18,320-byte comparator runtime `code`;
* `X` (`receiverAddress`) holds the registered synthetic fixture `Receiver.code`
  (`scripts/lift/certificates.json`, id `vplus-receiver`): coin 1 and the ETH receiver at once;
* the caller `S` has no code.

The top-level message: `S` calls the pool `P` with `remove_liquidity(100, [0, 0], X)`, value 0,
1,000,000 gas, Jaune depth 1024, empty accessed sets, as Jaune's `Frame.enter` enters it.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-- The pool the message enters: the ETH/stETH forwarder. -/
abbrev proxyAddress : Adr := curveStethPool847e
/-- The caller `S`. -/
abbrev senderAddress : Adr := Witness.callerAddress
/-- Coin 1 and the ETH receiver `X`. -/
def receiverAddress : Adr := 0xcccc000000000000000000000000000000000c0c

/-- The forwarder runtime at the pool address. -/
abbrev fwdCode : ByteArray := forwarderCode curvePlainImpl847e

/-- `remove_liquidity(uint256,uint256[2],address)` = `0x3eb1719f`, `(100, [0, 0], X)`. -/
def removeCall : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ Witness.word 100 ++ Witness.word 0 ++ Witness.word 0 ++
    Witness.word receiverAddress.toNat

/-- The pre-state's accounts without storage. -/
def acctsInit : List (Adr × Acct) :=
  [(proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩),
   (curvePlainImpl847e, ⟨1, 0, .empty, code⟩),
   (receiverAddress, ⟨1, 0, .empty, Receiver.code⟩),
   (senderAddress, ⟨1, 0, .empty, .empty⟩)]

def worldBase : State := stateFoldAcct default acctsInit

theorem storOf_worldBase (a : Adr) (k : B256) : storOf worldBase a k = 0 :=
  storOf_stateFoldAcct acctsInit a k

/-- The storage slot of the liquidity-token balance mapping entry `balanceOf[S]`: the pool
hashes the mapping's slot (20) and the key (`remove_liquidity` prints this preimage). -/
def balanceSlot : B256 :=
  12011451804723886938623838408310629856121848711978705641980654444407945751542

theorem balanceSlot_eq :
    balanceSlot = Bytes.keccak (Witness.word 20 ++ Witness.word senderAddress.toNat) := by
  decide +kernel

/-- The pool's storage: lock released (3), `coins[1] = X`, `totalSupply = 1000`, and the
caller's liquidity balance (`balanceOf[S] = 500`). -/
def poolInit : List ((Adr × B256) × B256) :=
  [((proxyAddress, (0 : Nat).toB256), (3 : Nat).toB256),
   ((proxyAddress, (3 : Nat).toB256), receiverAddress.toNat.toB256),
   ((proxyAddress, (0x16 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, balanceSlot), (500 : Nat).toB256)]

def worldInit : State := stateFoldStor worldBase poolInit

def acsInit : AcctShadow := acctShadowOf acctsInit

def storInit : StorShadow := storShadowOf poolInit

theorem storAgreeInit : ∀ a k, storOf worldInit a k = lookupS storInit a k :=
  storOf_stateFoldStor poolInit storOf_worldBase

theorem acctAgreeInit : AcctAgree worldInit acsInit :=
  acctAgree_stateFoldStor poolInit (acctAgree_stateFoldAcct acctsInit)

/-- The block environment: Prague (Jaune's default), the pre-state as original state. -/
def benvInit : BenvStat := { (default : BenvStat) with origState := worldInit }

/-- **The top-level message call.** -/
def msgTop : Msg where
  benv := ⟨worldInit, .emptyWithCapacity, benvInit⟩
  tenv := default
  caller := senderAddress
  target := some proxyAddress
  currentTarget := proxyAddress
  gas := 1000000
  value := 0
  data := removeCall
  codeAddress := some proxyAddress
  code := fwdCode
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- The top-level frame. -/
def frameTop : Frame := Frame.ofCall msgTop

/-- The machine the top-level frame enters with. -/
def eTop : Evm := match frameEnterS frameTop acsInit with | .run e => e | .done _ => default

theorem eTop_eq : frameEnterS frameTop acsInit = .run eTop := by kernel_rfl

/-- The forwarder frame's start configuration. -/
def cTop : PCfg := childCfg eTop frameTop [] [] storInit acsInit

theorem cTop_agree : PAgree cTop := by
  refine frameStart_agree .undefined eTop_eq (fun x => ?_) (fun a => ?_) (fun a k => ?_) ?_
  · show x ∈ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256)) ↔
      x ∈ ([] : List (Adr × B256))
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · show a ∈ (Std.HashSet.emptyWithCapacity : AdrSet) ↔ a ∈ ([] : List Adr)
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · exact storAgreeInit a k
  · exact acctAgreeInit

/-- The forwarder's code tries (depth 6 covers its 45 bytes). -/
def fwdTries : CodeTries fwdCode 6 :=
  CodeTries.ofCode fwdCode 6 (by decide) (by decide)

/-- The receiver's code tries (depth 7 covers its 86 bytes). -/
def receiverTries : CodeTries Receiver.code 7 :=
  CodeTries.ofCode Receiver.code 7 (by decide) (by decide)

/-- The receiver's lifted certificate checks against its bytes (its registration's check). -/
theorem Receiver.cert_check : Cert.check Receiver.code Receiver.cert = true := by decide +kernel

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2
