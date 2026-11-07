import Blanc.Lift.BuilderRequest.Exit.System
import Blanc.Lift.BuilderRequest.SystemCall
import Blanc.Lift.BuilderRequest.Exit.Creation.Address

/-!
# The exit builder's checked system call, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`. The published EIP-8282
text is not the reference where it differs from these bytes and `sys-asm` `83f9801`.

`system_call_ok` is the totality form: canonical code installed and `fork = .amsterdam`, any storage.
`SysCall.spec` at `sysCall` is its exact result. It does not claim that storage at activation has any shape, or
anything about a first Amsterdam block's transactions.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open Creation (address)

section offsets

variable {i : Nat} (hi : i < 16)
include hi

theorem off0_nat : (off0 i.toB256).toNat = 68 * i :=
  (mul_toB256_toNat_of_lt (a := 68) (n := i) (by omega) (by
    rw [show (68 : B256).toNat = 68 by decide]
    omega)).trans (by rw [show (68 : B256).toNat = 68 by decide])

theorem off1_nat : (off1 i.toB256).toNat = 20 + 68 * i :=
  lit_add_toNat (by decide) (off0_nat hi) (by omega)

theorem off2_nat : (off2 i.toB256).toNat = 52 + 68 * i :=
  (lit_add_toNat (n := 32) (by decide) (off1_nat hi) (by omega)).trans (by omega)

/-- A record's writes at their actual offsets. -/
theorem recordStage_eq (rd : B256 → B256) (h : B256) :
    recordStage rd h i.toB256 =
      [(68 * i, (rd (recordKey h i.toB256) <<< 96).toBytes),
       (20 + 68 * i, (rd (1 + recordKey h i.toB256)).toBytes),
       (52 + 68 * i, (rd (2 + recordKey h i.toB256)).toBytes)] := by
  simp only [recordStage]
  rw [off0_nat hi, off1_nat hi, off2_nat hi]

end offsets

/-- The allocation: 16 records of 68 bytes and the last word's 16 bytes past them, rounded up. -/
def sysMemory : SysMemory sysPath where
  alloc := 1120
  aligned := by decide
  lenN := 68
  len_word := by decide
  len_le := by decide
  windows := fun rd h i hi w hw => by
    have hi' : i < 16 := hi
    show w.1 + w.2 ≤ 1120
    change w ∈ MemoryStage.footprint (recordStage rd h i.toB256) at hw
    rw [recordStage_eq hi' rd h] at hw
    simp only [MemoryStage.footprint, List.map_cons, List.map_nil, B256.length_toBytes,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega
  alloc_lt := by decide

/-- The bound on the system call's execution gas, from the rule record: 16 records of three reads and three writes, four more reads, four stores, the allocation's expansion. The state
gas is separate: it draws on the reservoir. -/
theorem frameBound_le : sysPath.frameBound sysMemory.alloc ≤ 161000 := by decide

/-- The checked exit system call returns and uses at most 161,000 gas. -/
def SystemCallOk (benv : Benv) : Prop :=
  ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
    systemTransactionGas - out.gasLeft ≤ 161000

/-- The exit runtime's system call facts. -/
def sysCall : SysCall sysPath where
  memory := sysMemory
  target := address
  bound := 161000
  nonempty := by decide +kernel
  size_ne := by decide +kernel
  not_precompile := by decide
  bound_le := frameBound_le
  room := by decide

/-- **The exit builder's system call succeeds, from any storage.** Under Amsterdam, with the canonical
code installed, the checked system call returns and uses at most 161,000 of its 30,000,000 gas.
There is no storage premise. -/
theorem system_call_ok {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) : SystemCallOk benv :=
  let h := sysCall.spec hfork installed
  ⟨_, _, h.1, h.2⟩

end Blanc.Lift.BuilderRequest.Exit
