import Blanc.Lift.VyperNonreentrantDeployed.ProxyEntry
import Blanc.ConcreteRun

/-!
Concrete machine states for the kernel-stepping pilot on the exact 0.2.15
implementation (`kernel-stepping-pilot-v1`). The storage values are
arbitrary but concrete; they are measurement fixtures, not a scenario claim.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Concrete

open Jaune Blanc.ConcreteRun

/-- A big-endian 32-byte ABI word. -/
def word (n : Nat) : Bytes :=
  (List.range 32).reverse.map fun i => ((n >>> (8 * i)) % 256).toUInt8

def attacker : Adr := 0xa11ce00000000000000000000000000000000a11
def receiver : Adr := 0xa11ce00000000000000000000000000000000a11

/-- `remove_liquidity(uint256,uint256[2],address)` = `0x3eb1719f`,
with `(200, [0, 0], receiver)`: 132 bytes. -/
def removeCalldata : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ word 200 ++ word 0 ++ word 0 ++ word receiver.toNat

/-- Arbitrary concrete pool storage at the proxy (the storage owner). -/
def poolStorage : List (Nat × Nat) :=
  [(1, 0xfac7),
   (3, 0xae7ab96520de3a18e5e111b5eaab095312d7fe84),
   (4, 1000000), (5, 900000), (6, 4000000), (7, 20000), (8, 20000),
   (9, 0), (10, 0), (11, 1000000000000000000), (12, 1000000000000000000),
   (0x1d, 1800), (0x1a, 1800)]

def poolState : State :=
  poolStorage.foldl (fun w kv => w.setStorVal proxyAddress kv.1.toB256 kv.2.toB256)
    (.empty : State)

def implSevmWith (code : ByteArray) (data : Bytes) : Sevm :=
  { (default : Sevm) with
    caller := attacker
    currentTarget := proxyAddress
    target := some proxyAddress
    gas := 10000000
    data := data
    codeAddress := some implementationAddress
    code := code
    depth := 1022 }

def implSevm (data : Bytes) : Sevm := implSevmWith implementationCode data

def implDevm (gas : Nat) (world : State) : Devm :=
  ((default : Devm).withGasLeft gas).withState world

/-- The proxy frame entry with the same calldata. -/
def proxySevm (data : Bytes) : Sevm :=
  { (default : Sevm) with
    caller := attacker
    currentTarget := proxyAddress
    target := some proxyAddress
    gas := 10000000
    data := data
    codeAddress := some proxyAddress
    code := proxyCode
    depth := 1023 }

/-- A literal mid-frame state: given pc, stack words, gas and memory bytes,
over the implementation code with `add_liquidity` calldata. -/
def midStateWith (code : ByteArray) (data : Bytes) (pc : Nat) (stack : List Nat) (gas : Nat) (mem : List Nat) : Evm :=
  ⟨pc, implSevmWith code data,
    (((implDevm gas poolState).withStack (stack.map Nat.toB256)).withMemory
      ⟨(mem.map Nat.toUInt8).toArray, mem.length⟩)⟩

end Blanc.Lift.VyperNonreentrantDeployed.Concrete
