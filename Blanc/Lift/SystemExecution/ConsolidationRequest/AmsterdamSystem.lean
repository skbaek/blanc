import Blanc.Lift.SystemExecution.ConsolidationRequest.Jumps
import Blanc.Lift.RequestSystem.Call
import Blanc.Lift.RequestSystem.BodySegs
import Blanc.Lift.RequestSystem.PlainExcess

/-!
# The EIP-7251 runtime's system path, under Amsterdam

The runtime as an instance of `SysPath`: cap 2, target 1, four slots and 116 returned bytes per record. The
record body reads four words and writes four overlapping windows. Any storage, any memory. The checked
system call then succeeds from any storage, on the full path, not only on an empty queue.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.SystemExecution.ConsolidationRequest.Amsterdam

open Jaune
open RequestSystem

/-- The excess arm's words. -/
def sysWords : PlainWords where
  over := ⟨0x01, [0x73], by decide⟩
  carry := ⟨0x01, [0x88], by decide⟩
  final := ⟨0x01, [0x8e], by decide⟩
  target := ⟨0x01, [], by decide⟩
  len := ⟨0x74, [], by decide⟩
  overIdx := 3
  finalIdx := 4

/-- The runtime's system-path shape. -/
def sysShape : SysShape :=
  plainShape sysWords ⟨0xe7, [], by decide⟩ ⟨0x02, [], by decide⟩ ⟨0x01, [0x29], by decide⟩
    ⟨0x01, [0x3b], by decide⟩ ⟨0x01, [0x46], by decide⟩ 1 2

/-- A record's first storage key. -/
def recordKey (h i : B256) : B256 := (4 : B256) + (4 : B256) * (i + h)

/-- The keys a record's body reads. -/
def recordKeys (h i : B256) : List B256 :=
  [recordKey h i, 1 + recordKey h i, 2 + recordKey h i, 3 + recordKey h i]

/-- The memory offsets, from the record's index. -/
def off0 (i : B256) : B256 := (116 : B256) * i
def off1 (i : B256) : B256 := 20 + off0 i
def off2 (i : B256) : B256 := 32 + off1 i
def off3 (i : B256) : B256 := 32 + off2 i

/-- A record's four memory writes, in execution order. -/
def recordStage (rd : B256 → B256) (h i : B256) : MemoryStage :=
  [((off0 i).toNat, (rd (recordKey h i) <<< 96).toBytes),
   ((off1 i).toNat, (rd (1 + recordKey h i)).toBytes),
   ((off2 i).toNat, (rd (2 + recordKey h i)).toBytes),
   ((off3 i).toNat, (rd (3 + recordKey h i)).toBytes)]

theorem entry6 : cert.prog[6]? = some (sysHeader sysShape t_00f1_c1) := rfl

/-- **One exact iteration of the certified drain**, ending on the loop's back-edge. Any storage, any
memory. -/
theorem body_run {sevm : Sevm} {b : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (next : SFunc.RunExact cert.prog sevm
      (St (readsBase sevm b (recordKeys h i)) [(1 : B256) + i, c, h, t]
        ((recordStage (b.getStorVal sevm.currentTarget) h i).applyMemory M) gas)
      (sysHeader sysShape t_00f1_c1) oc) :
    SFunc.RunExact cert.prog sevm
      (St b [i, c, h, t] M (gas + 117 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage (b.getStorVal sevm.currentTarget) h i) M)) t_00f1_c1 oc := by
  generalize hrd : b.getStorVal sevm.currentTarget = rd at next ⊢
  have hv : ∀ k, b.getStorVal sevm.currentTarget k = rd k := fun k => by rw [hrd]
  generalize hr1 : afterSloadA sevm b (recordKey h i) = r1
  generalize hr2 : afterSloadA sevm r1 (1 + recordKey h i) = r2
  generalize hr3 : afterSloadA sevm r2 (2 + recordKey h i) = r3
  have hreads : readsBase sevm b (recordKeys h i) = afterSloadA sevm r3 (3 + recordKey h i) := by
    subst hr3 hr2 hr1
    rfl
  rw [hreads] at next
  generalize hM1 : M.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes = M1
  generalize hM2 : M1.write (off1 i).toNat (rd (1 + recordKey h i)).toBytes = M2
  generalize hM3 : M2.write (off2 i).toNat (rd (2 + recordKey h i)).toBytes = M3
  have happly : (recordStage rd h i).applyMemory M =
      M3.write (off3 i).toNat (rd (3 + recordKey h i)).toBytes := by
    subst hM3 hM2 hM1
    simp only [recordStage, MemoryStage.applyMemory, List.foldl]
  rw [happly] at next
  have hgas : MemoryStage.selectedGas (recordStage rd h i) M =
      chg M (off0 i) 32 + chg M1 (off1 i) 32 + chg M2 (off2 i) 32 + chg M3 (off3 i) 32 := by
    subst hM3 hM2 hM1
    simp only [recordStage, MemoryStage.selectedGas, B256.length_toBytes, chg]
    omega
  have tail : SFunc.RunExact cert.prog sevm
      (St (afterSloadA sevm r3 (3 + recordKey h i)) [i, c, h, t]
        (M3.write (off3 i).toNat (rd (3 + recordKey h i)).toBytes) (gas + 17))
      (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.push [0xe9] (by decide))
        (.jump 6)))) oc := by
    have e : gas + 17 = gas + 8 + 3 + 3 + 3 := by omega
    rw [e]
    apply rx_push (w := (1 : B256)) (by decide) (by rroom)
    apply rx_add' rfl (by rroom)
    apply rx_push rfl (by rroom)
    exact rx_jump entry6 next
  have s3 := seg_last (k := 0x03) (kv := 3) (M := M3) (b := r3) (o := off3 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (3 + recordKey h i)) (le := by decide) hacc (by decide) (by rroom)
    (by subst hr3 hr2 hr1; simp only [afterSloadA_getStorVal, hv]) tail
  have s2 := seg_word (k := 0x02) (kv := 2) (M := M2) (b := r2) (o := off2 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (2 + recordKey h i)) (le1 := by decide) (le2 := by decide) hacc
    (by decide) (by rroom) (by subst hr2 hr1; simp only [afterSloadA_getStorVal, hv])
    (by rw [hr3, hM3]; exact s3)
  have s1 := seg_word (k := 0x01) (kv := 1) (M := M1) (b := r1) (o := off1 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (1 + recordKey h i)) (le1 := by decide) (le2 := by decide) hacc
    (by decide) (by rroom) (by subst hr1; simp only [afterSloadA_getStorVal, hv])
    (by rw [hr2, hM2]; exact s2)
  have s0 := seg_source (M := M) (b := b) (o := off0 i) (key := recordKey h i) (T := [i, c, h, t])
    (le1 := by decide) (le2 := by decide) hacc hsh (by rroom) (hv _) (by rw [hr1, hM1]; exact s1)
  have st := seg_start (w := 0x04) (wv := 4) (l := 0x74) (lv := 116) (i := i) (c := c) (h := h) (t := t)
    (le1 := by decide) (le2 := by decide) (le3 := by decide) (by decide) (by decide) s0
  have e : ∀ g, gas + 117 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M = g →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M g) t_00f1_c1 oc →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M (gas + 117 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M)) t_00f1_c1 oc := fun _ hg r => hg ▸ r
  refine e _ ?_ st
  rw [hgas]
  subst hr3 hr2 hr1
  simp only [readsGas, recordKeys]
  omega

/-- The runtime's system path. -/
def sysPath : SysPath where
  code := consolidationRequestCode
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape := sysShape
  systemDest := ⟨0xd3, [], by decide⟩
  user := t_001a_c0
  body := t_00f1_c1
  capN := 2
  cap_word := by decide
  slots := 4
  writes := 4
  bodyFixed := 117
  keys := recordKeys
  keys_length := fun _ _ => rfl
  stage := recordStage
  stage_length := fun _ _ _ => rfl
  root := rfl
  entry := rfl
  excessEntry := rfl
  excess_run := fun hacc hpush0 _ next => plain_excess_run sysWords hacc hpush0 rfl rfl next
  body_run := fun hacc hsh next => body_run hacc hsh next

section offsets

variable {i : Nat} (hi : i < 2)
include hi

theorem off0_nat : (off0 i.toB256).toNat = 116 * i :=
  (mul_toB256_toNat_of_lt (a := 116) (n := i) (by omega) (by
    rw [show (116 : B256).toNat = 116 by decide]
    omega)).trans (by rw [show (116 : B256).toNat = 116 by decide])

theorem off1_nat : (off1 i.toB256).toNat = 20 + 116 * i :=
  lit_add_toNat (by decide) (off0_nat hi) (by omega)

theorem off2_nat : (off2 i.toB256).toNat = 52 + 116 * i :=
  (lit_add_toNat (n := 32) (by decide) (off1_nat hi) (by omega)).trans (by omega)

theorem off3_nat : (off3 i.toB256).toNat = 84 + 116 * i :=
  (lit_add_toNat (n := 32) (by decide) (off2_nat hi) (by omega)).trans (by omega)

/-- A record's writes at their actual offsets. -/
theorem recordStage_eq (rd : B256 → B256) (h : B256) :
    recordStage rd h i.toB256 =
      [(116 * i, (rd (recordKey h i.toB256) <<< 96).toBytes),
       (20 + 116 * i, (rd (1 + recordKey h i.toB256)).toBytes),
       (52 + 116 * i, (rd (2 + recordKey h i.toB256)).toBytes),
       (84 + 116 * i, (rd (3 + recordKey h i.toB256)).toBytes)] := by
  simp only [recordStage]
  rw [off0_nat hi, off1_nat hi, off2_nat hi, off3_nat hi]

end offsets

/-- The allocation: two records of 116 bytes, which ends on their last word, rounded up. -/
def sysMemory : SysMemory sysPath where
  alloc := 256
  aligned := by decide
  lenN := 116
  len_word := by decide
  len_le := by decide
  windows := fun rd h i hi w hw => by
    have hi' : i < 2 := hi
    show w.1 + w.2 ≤ 256
    change w ∈ MemoryStage.footprint (recordStage rd h i.toB256) at hw
    rw [recordStage_eq hi' rd h] at hw
    simp only [MemoryStage.footprint, List.map_cons, List.map_nil, B256.length_toBytes,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega
  alloc_lt := by decide

/-- The bound on the system call's execution gas, from the rule record: two records of four reads and
four writes, four more reads, four stores, the allocation's expansion. The state gas is separate: it
draws on the reservoir. -/
theorem frameBound_le : sysPath.frameBound sysMemory.alloc ≤ 75000 := by decide

/-- The runtime's system call facts. -/
def sysCall : SysCall sysPath where
  memory := sysMemory
  target := consolidationRequestPredeployAddress
  bound := 75000
  nonempty := by decide +kernel
  size_ne := by decide +kernel
  not_precompile := by decide
  bound_le := frameBound_le
  room := by decide

/-- **The EIP-7251 system call succeeds under Amsterdam, from any storage.** With the canonical code
installed, the checked system call returns, its post state is `sysState`, and it uses at most 75,000 of
its 30,000,000 gas. There is no storage premise. -/
theorem system_call_ok {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode) :
    ∃ out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] =
        .ok (sysState sysShape benv.state consolidationRequestPredeployAddress, out) ∧
      systemTransactionGas - out.gasLeft ≤ 75000 :=
  let h := sysCall.spec hfork installed
  ⟨_, h.1, h.2⟩

end Blanc.Lift.SystemExecution.ConsolidationRequest.Amsterdam
