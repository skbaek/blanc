import Blanc.Lift.BuilderRequest.Deposit.System
import Blanc.Lift.BuilderRequest.SystemCall
import Blanc.Lift.BuilderRequest.Deposit.Creation.Address

/-!
# The deposit builder's checked system call, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`. The published EIP-8282
text is not the reference where it differs from these bytes and `sys-asm` `83f9801`.

`system_call_ok` is the totality form: canonical code installed and `fork = .amsterdam`, any storage.
`SysCall.spec` at `sysCall` is its exact result. It does not claim that storage at activation has any shape, or
anything about a first Amsterdam block's transactions.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open Creation (address)

section offsets

variable {i : Nat} (hi : i < 64)
include hi

theorem off0_nat : (off0 i.toB256).toNat = 184 * i :=
  (mul_toB256_toNat_of_lt (a := 184) (n := i) (by omega) (by
    rw [show (184 : B256).toNat = 184 by decide]
    omega)).trans (by rw [show (184 : B256).toNat = 184 by decide])

theorem off1_nat : (off1 i.toB256).toNat = 32 + 184 * i :=
  lit_add_toNat (by decide) (off0_nat hi) (by omega)

theorem off2_nat : (off2 i.toB256).toNat = 64 + 184 * i :=
  (lit_add_toNat (n := 32) (by decide) (off1_nat hi) (by omega)).trans (by omega)

theorem amountAt_nat : (amountAt i.toB256).toNat = 80 + 184 * i :=
  (lit_add_toNat (n := 16) (by decide) (off2_nat hi) (by omega)).trans (by omega)

theorem off3_nat : (off3 i.toB256).toNat = 96 + 184 * i :=
  (lit_add_toNat (n := 32) (by decide) (off2_nat hi) (by omega)).trans (by omega)

theorem off4_nat : (off4 i.toB256).toNat = 128 + 184 * i :=
  (lit_add_toNat (n := 32) (by decide) (off3_nat hi) (by omega)).trans (by omega)

theorem off5_nat : (off5 i.toB256).toNat = 160 + 184 * i :=
  (lit_add_toNat (n := 32) (by decide) (off4_nat hi) (by omega)).trans (by omega)

/-- A record's writes at their actual offsets. -/
theorem recordStage_eq (rd : B256 → B256) (h : B256) :
    let key := recordKey h i.toB256
    let a := amountOf (rd (2 + key))
    recordStage rd h i.toB256 =
      [(184 * i, (rd key).toBytes),
       (32 + 184 * i, (rd (1 + key)).toBytes),
       (64 + 184 * i, (rd (2 + key)).toBytes),
       (87 + 184 * i, [(a >>> 56).2.2.toUInt8]),
       (86 + 184 * i, [(a >>> 48).2.2.toUInt8]),
       (85 + 184 * i, [(a >>> 40).2.2.toUInt8]),
       (84 + 184 * i, [(a >>> 32).2.2.toUInt8]),
       (83 + 184 * i, [(a >>> 24).2.2.toUInt8]),
       (82 + 184 * i, [(a >>> 16).2.2.toUInt8]),
       (81 + 184 * i, [(a >>> 8).2.2.toUInt8]),
       (80 + 184 * i, [a.2.2.toUInt8]),
       (96 + 184 * i, (rd (3 + key)).toBytes),
       (128 + 184 * i, (rd (4 + key)).toBytes),
       (160 + 184 * i, (rd (5 + key)).toBytes)] := by
  intro key a
  have hb : ∀ (l : B256) (n m : Nat), l.toNat = n → n ≤ 7 → n + 80 = m →
      (l + amountAt i.toB256).toNat = m + 184 * i := fun l n m hl hn hm =>
    (lit_add_toNat hl (amountAt_nat hi) (by omega)).trans (by omega)
  simp only [recordStage]
  rw [off0_nat hi, off1_nat hi, off2_nat hi, hb 7 7 87 (by decide) (by decide) rfl,
    hb 6 6 86 (by decide) (by decide) rfl, hb 5 5 85 (by decide) (by decide) rfl,
    hb 4 4 84 (by decide) (by decide) rfl, hb 3 3 83 (by decide) (by decide) rfl,
    hb 2 2 82 (by decide) (by decide) rfl, hb 1 1 81 (by decide) (by decide) rfl,
    amountAt_nat hi, off3_nat hi, off4_nat hi, off5_nat hi]

end offsets

/-- The allocation: 64 records of 184 bytes and the last word's 8 bytes past them, rounded up. -/
def sysMemory : SysMemory sysPath where
  alloc := 11808
  aligned := by decide
  lenN := 184
  len_word := by decide
  len_le := by decide
  windows := fun rd h i hi w hw => by
    have hi' : i < 64 := hi
    show w.1 + w.2 ≤ 11808
    change w ∈ MemoryStage.footprint (recordStage rd h i.toB256) at hw
    rw [recordStage_eq hi' rd h] at hw
    simp only [MemoryStage.footprint, List.map_cons, List.map_nil, B256.length_toBytes,
      List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only <;> omega
  alloc_lt := by decide

/-- The bound on the system call's execution gas, from the rule record: 64 records of six reads and fourteen writes, four more reads, four stores, the allocation's expansion. The state
gas is separate: it draws on the reservoir. -/
theorem frameBound_le : sysPath.frameBound sysMemory.alloc ≤ 888000 := by decide

/-- The checked deposit system call returns and uses at most 888,000 gas. -/
def SystemCallOk (benv : Benv) : Prop :=
  ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
    systemTransactionGas - out.gasLeft ≤ 888000

/-- The deposit runtime's system call facts. -/
def sysCall : SysCall sysPath where
  memory := sysMemory
  target := address
  bound := 888000
  nonempty := by decide +kernel
  size_ne := by decide +kernel
  not_precompile := by decide
  bound_le := frameBound_le
  room := by decide

/-- **The deposit builder's system call succeeds, from any storage.** Under Amsterdam, with the canonical
code installed, the checked system call returns and uses at most 888,000 of its 30,000,000 gas.
There is no storage premise. -/
theorem system_call_ok {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) : SystemCallOk benv :=
  let h := sysCall.spec hfork installed
  ⟨_, _, h.1, h.2⟩

end Blanc.Lift.BuilderRequest.Deposit
