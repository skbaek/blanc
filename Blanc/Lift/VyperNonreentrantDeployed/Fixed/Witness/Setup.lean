import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exclusion
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.CheckTries
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reader.Cert
import Blanc.Lift.NodeWalk

/-!
# V+ nonvacuity witness: the pre-state and the top-level message

The explicit Prague pre-state of the V+ witness (EELS trace:
`scripts/lift/witness/vplus_run.py`, an untrusted printer):

* the pool `I = 0x847e…ed9` itself (`vplus_exclusion_impl`, `P = I`, no forwarder) holds
  the deployed 18,320-byte comparator runtime `code`, 1000 wei, and the storage
  lock (slot 0) = 3 (released), `coins[1]` (slot 3) = `R`, `totalSupply` (slot 0x16) = 1000;
* `R` (`readerAddress`) holds the registered synthetic 41-byte fixture `Reader.code`
  (`scripts/lift/certificates.json`, id `vplus-reader`): on any call it `STATICCALL`s `I`
  with `get_virtual_price()` (a guarded view) and `STOP`s;
* the caller `S` has no code.

The top-level message: `S` calls `I` with `remove_liquidity(100, [0, 0], S)`, value 0,
1,000,000 gas, Jaune depth 1024, empty accessed sets, as Jaune's `Frame.enter` enters it.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-- The pool: the implementation address itself. -/
abbrev poolAddress : Adr := curvePlainImpl847e
/-- The caller `S`. -/
def callerAddress : Adr := 0xaaaa000000000000000000000000000000000a11
/-- The coin-1 contract `R`. -/
def readerAddress : Adr := 0xbbbb000000000000000000000000000000000b0b

/-- A big-endian 32-byte ABI word. -/
def word (n : Nat) : Bytes :=
  (List.range 32).reverse.map fun i => ((n >>> (8 * i)) % 256).toUInt8

/-- `remove_liquidity(uint256,uint256[2],address)` = `0x3eb1719f`, `(100, [0, 0], S)`. -/
def removeCalldata : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ word 100 ++ word 0 ++ word 0 ++ word callerAddress.toNat

/-- The pre-state's accounts without storage. -/
def accts0 : List (Adr × Acct) :=
  [(poolAddress, ⟨1, (1000 : Nat).toB256, .empty, code⟩),
   (readerAddress, ⟨1, 0, .empty, Reader.code⟩),
   (callerAddress, ⟨1, 0, .empty, .empty⟩)]

def world0_base : State := stateFoldAcct default accts0

theorem storOf_world0_base (a : Adr) (k : B256) : storOf world0_base a k = 0 :=
  storOf_stateFoldAcct accts0 a k

/-- The pool's storage: lock released (3), `coins[1] = R`, `totalSupply = 1000`. -/
def poolWrites : List ((Adr × B256) × B256) :=
  [((poolAddress, (0 : Nat).toB256), (3 : Nat).toB256),
   ((poolAddress, (3 : Nat).toB256), readerAddress.toNat.toB256),
   ((poolAddress, (0x16 : Nat).toB256), (1000 : Nat).toB256)]

def world0 : State := stateFoldStor world0_base poolWrites

def acs0 : AcctShadow := acctShadowOf accts0

def stor0 : StorShadow := storShadowOf poolWrites

theorem storAgree0 : ∀ a k, storOf world0 a k = lookupS stor0 a k :=
  storOf_stateFoldStor poolWrites storOf_world0_base

theorem acctAgree0 : AcctAgree world0 acs0 :=
  acctAgree_stateFoldStor poolWrites (acctAgree_stateFoldAcct accts0)

/-- The block environment: Prague (Jaune's default), the pre-state as original state. -/
def benvStat0 : BenvStat := { (default : BenvStat) with origState := world0 }

/-- **The top-level message call.** -/
def msg0 : Msg where
  benv := ⟨world0, .emptyWithCapacity, benvStat0⟩
  tenv := default
  caller := callerAddress
  target := some poolAddress
  currentTarget := poolAddress
  gas := 1000000
  value := 0
  data := removeCalldata
  codeAddress := some poolAddress
  code := code
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- The top-level frame. -/
def f0 : Frame := Frame.ofCall msg0

/-- The machine the top-level frame enters with. -/
def e0 : Evm := match frameEnterS f0 acs0 with | .run e => e | .done _ => default

theorem e0_eq : frameEnterS f0 acs0 = .run e0 := by kernel_rfl

/-- The pool frame's start configuration. -/
def c0 : PCfg := childCfg e0 f0 [] [] stor0 acs0

theorem c0_agree : PAgree c0 := by
  refine frameStart_agree .undefined e0_eq (fun x => ?_) (fun a => ?_) (fun a k => ?_) ?_
  · show x ∈ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256)) ↔
      x ∈ ([] : List (Adr × B256))
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · show a ∈ (Std.HashSet.emptyWithCapacity : AdrSet) ↔ a ∈ ([] : List Adr)
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · exact storAgree0 a k
  · exact acctAgree0

/-- The fixture's code tries (depth 6 covers its 41 bytes). -/
def readerTries : CodeTries Reader.code 6 :=
  CodeTries.ofCode Reader.code 6 (by decide) (by decide)

/-- The fixture's lifted certificate checks against its bytes (its registration's check). -/
theorem Reader.cert_check : Cert.check Reader.code Reader.cert = true := by decide +kernel

/-- Static facts of the top-level machine (closed evaluation). -/
theorem e0_facts : (e0.pc, e0.sta.currentTarget, e0.sta.code, e0.sta.benvStat.fork) =
    (0, poolAddress, code, .prague) := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness
