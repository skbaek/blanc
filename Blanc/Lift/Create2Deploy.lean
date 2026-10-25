import Blanc.Lift.Deploy
import Blanc.ForwardCall

/-!
# Shared `CREATE2` state and address helpers

Contract-neutral definitions for the init-code slice, address digest, opcode
charge, prepared parent, collision predicate and successful resumed state.
Historical opcode composition is provided by `HistCreate.lean`.
-/

namespace Blanc.Lift

open Jaune

/-- The CREATE2 address computed from the init-code digest `hash`. -/
def create2AddressOfHash (sender : Adr) (salt hash : B256) : Adr :=
  (Bytes.keccak ((0xFF : UInt8) :: (sender.toBytes ++ salt.toBytes ++ hash.toBytes))).toAdr

/-- Jaune's CREATE2 address is the digest view at the digest of the init code. -/
theorem create2NewAddress_eq_ofHash (sender : Adr) (salt : B256) (initCode : Bytes) :
    create2NewAddress sender salt initCode =
      create2AddressOfHash sender salt (Bytes.keccak initCode) := rfl

/-- The init code a `CREATE2` from memory `M` reads: the window `[i, i + sz)` of the extended
memory. -/
def create2InitCode (M : Mem) (i sz : B256) : Bytes :=
  (M.extends [⟨i.toNat, sz.toNat⟩]).data.sliceD i.toNat sz.toNat 0

/-- The parent after `CREATE2`'s charge and memory extension, the withheld child gas, cleared
return data, the creator's nonce bump and the warm access of the new address. -/
def create2Prepared (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (i sz : B256)
    (addr : Adr) : Devm :=
  let d := (St b S M G).memExtends [⟨i.toNat, sz.toNat⟩]
  addAccessedAddress (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
    []).incrNonce sevm.currentTarget) addr

/-- `CREATE2`'s own charge from memory `M`: access, init-code hashing, memory expansion and the
init-code word charge. -/
def create2Charge (sevm : Sevm) (M : Mem) (i sz : B256) : Nat :=
  sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv sz.toNat 32 +
    (calculateMemoryGasCost (memExtsSize M.size [⟨i.toNat, sz.toNat⟩]) -
      calculateMemoryGasCost M.size) + gasInitCodeWordCost * ceilDiv sz.toNat 32

/-- The `CREATE2` collision check passes: the target has no nonce, code or storage. -/
def Create2TargetEmpty (d : Devm) (a : Adr) : Prop :=
  (d.state.get a).nonce = 0 ∧ (d.state.get a).code.size = 0 ∧ (d.state.get a).stor.size = 0

/-- The parent after a successful creation resumes: the child's world and gas incorporated, empty
return data, and the new address on the stack. -/
def create2Post (D child : Devm) (addr : Adr) : Devm :=
  let d := incorporateChildOnSuccess D child []
  d.setMach ⟨addr.toB256 :: d.stack, d.memory, d.gasLeft, d.stateGas⟩

end Blanc.Lift
