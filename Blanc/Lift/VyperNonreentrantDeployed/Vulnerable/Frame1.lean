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

/-- The pool account `P`: the 45-byte proxy, 1000 wei, the pool storage. -/
def poolAcct : Acct :=
  { nonce := 1, bal := (1000 : Nat).toB256, code := proxyCode,
    stor := poolStorage.foldl (fun s kv => Std.TreeMap.insert s kv.1.toB256 kv.2.toB256) .empty }

/-- The world, built by `Std.TreeMap.insert` (kernel-reducible, unlike `State.set`). -/
def world0 : State := Std.TreeMap.insert .empty proxyAddress poolAcct

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
    depth := 1
    benvStat := { (default : BenvStat) with origState := world0 } }

/-- Frame 1's entry machine: the proxy's `DELEGATECALL` has warmed the implementation
address (the top-level message starts with empty accessed sets, as in the preflight). -/
def pre1 : Devm :=
  addAccessedAddress (((default : Devm).withGasLeft gas1).withState world0) implementationAddress

def c0 : Cfg := ⟨pre1, t_0000_c0, [], [], [implementationAddress]⟩

theorem c0_agree : Agree c0 := by
  refine ⟨fun x => ?_, fun a => ?_⟩
  · show x ∈ (default : Devm).accessedStorageKeys ↔ x ∈ ([] : List (Adr × B256))
    simp [show (default : Devm).accessedStorageKeys = .emptyWithCapacity from rfl]
  · show a ∈ (default : Devm).accessedAddresses.insert implementationAddress ↔
      a ∈ [implementationAddress]
    rw [Std.HashSet.mem_insert, List.mem_singleton, beq_iff_eq,
      show (default : Devm).accessedAddresses = .emptyWithCapacity from rfl]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, or_false]
    exact ⟨Eq.symm, Eq.symm⟩

/-- The observed projection a chunk decision pins: gas, stack and memory bytes. -/
def summ : Res → Option (Nat × List Nat × List Nat)
  | .cont c => some (c.devm.gasLeft, c.devm.stack.map B256.toNat,
      c.devm.memory.data.toList.map UInt8.toNat)
  | _ => none

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
