import Blanc.Lift.WithdrawalRequest.Jumps
import Blanc.Lift.RequestSystem.Call
import Blanc.Lift.RequestSystem.BodySegs
import Blanc.Lift.RequestSystem.PlainExcess

/-!
# The EIP-7002 runtime's system path, under Amsterdam

The runtime as an instance of `SysPath`: cap 16, target 2, three slots and 76 returned bytes per record.
The record body reads three words and writes eleven windows: the source address at the top of its word,
the public key's first word, its last 16 bytes masked, then the amount's eight bytes little-endian. Any
storage, any memory. The checked system call then succeeds from any storage, with no storage premise.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`. This module says nothing
about the covered forks, whose theorems stay in this family's other modules.
-/

namespace Blanc.Lift.WithdrawalRequest.Amsterdam

open Jaune
open RequestSystem

/-- The excess arm's words. -/
def sysWords : PlainWords where
  over := ⟨0x01, [0xcd], by decide⟩
  carry := ⟨0x01, [0xe2], by decide⟩
  final := ⟨0x01, [0xe8], by decide⟩
  target := ⟨0x02, [], by decide⟩
  len := ⟨0x4c, [], by decide⟩
  overIdx := 3
  finalIdx := 4

/-- The runtime's system-path shape. -/
def sysShape : SysShape :=
  plainShape sysWords ⟨0xdf, [], by decide⟩ ⟨0x10, [], by decide⟩ ⟨0x01, [0x83], by decide⟩
    ⟨0x01, [0x95], by decide⟩ ⟨0x01, [0xa0], by decide⟩ 1 2

/-- A record's first storage key. -/
def recordKey (h i : B256) : B256 := (4 : B256) + (3 : B256) * (i + h)

/-- The keys a record's body reads. -/
def recordKeys (h i : B256) : List B256 := [recordKey h i, 1 + recordKey h i, 2 + recordKey h i]

/-- The memory offsets, from the record's index. -/
def off0 (i : B256) : B256 := (76 : B256) * i
def off1 (i : B256) : B256 := 20 + off0 i
def off2 (i : B256) : B256 := 32 + off1 i
def amountAt (i : B256) : B256 := 16 + off2 i

/-- The mask keeping a packed word's top 16 bytes. -/
def keyMask : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00]

/-- A record's eleven memory writes, in execution order. -/
def recordStage (rd : B256 → B256) (h i : B256) : MemoryStage :=
  let key := recordKey h i
  let a := rd (2 + key) >>> 64
  [((off0 i).toNat, (rd key <<< 96).toBytes),
   ((off1 i).toNat, (rd (1 + key)).toBytes),
   ((off2 i).toNat, (keyMask &&& rd (2 + key)).toBytes),
   (((7 : B256) + amountAt i).toNat, [(a >>> 56).2.2.toUInt8]),
   (((6 : B256) + amountAt i).toNat, [(a >>> 48).2.2.toUInt8]),
   (((5 : B256) + amountAt i).toNat, [(a >>> 40).2.2.toUInt8]),
   (((4 : B256) + amountAt i).toNat, [(a >>> 32).2.2.toUInt8]),
   (((3 : B256) + amountAt i).toNat, [(a >>> 24).2.2.toUInt8]),
   (((2 : B256) + amountAt i).toNat, [(a >>> 16).2.2.toUInt8]),
   (((1 : B256) + amountAt i).toNat, [(a >>> 8).2.2.toUInt8]),
   ((amountAt i).toNat, [a.2.2.toUInt8])]

section seg

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome} {M : Mem} {G : Nat}

/-- `SWAP1 PUSH1 2 ADD SLOAD DUP1 PUSH32 mask AND DUP3 MSTORE SWAP1 PUSH1 0x10 ADD SWAP1 PUSH1 0x40 SHR
SWAP1`: the packed word's key bytes stored, leaving the amount's byte pointer over the amount. -/
theorem seg_packed {o key v : B256} {T : List B256} {le1 le2 le3 le4}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (hroom : T.length ≤ 1000) (hv : b.getStorVal sevm.currentTarget ((2 : B256) + key) = v)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b ((2 : B256) + key)) (((16 : B256) + o) :: (v >>> 64) :: T)
        (M.write o.toNat (keyMask &&& v).toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 42 + chg M o 32 + sloadCost sevm b ((2 : B256) + key)))
      (.next (.reg (.swap 0)) (.next (.push [0x02] le1) (.next (.reg .add) (.next (.reg .sload)
        (.next (.reg (.dup 0)) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] le2)
        (.next (.reg .and) (.next (.reg (.dup 2)) (.next (.reg .mstore) (.next (.reg (.swap 0))
        (.next (.push [0x10] le3) (.next (.reg .add) (.next (.reg (.swap 0))
        (.next (.push [0x40] le4) (.next (.reg .shr) (.next (.reg (.swap 0)) f)))))))))))))))) oc := by
  have e : G + 42 + chg M o 32 + sloadCost sevm b ((2 : B256) + key) =
      G + 3 + 3 + 3 + 3 + 3 + 3 + 3 + chg M o 32 + 3 + 3 + 3 + 3 + sloadCost sevm b ((2 : B256) + key)
        + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_swap1
  apply rx_push (w := (2 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_sloadV hacc (by rroom) hv
  apply rx_dup1 (by rroom)
  apply rx_push (w := keyMask) rfl (by rroom)
  apply rx_and rfl (by rroom)
  apply rx_dup3 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_swap1
  apply rx_push (w := (16 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_swap1
  apply rx_push (w := (64 : B256)) (by decide) (by rroom)
  apply rx_shr (v := v >>> 64) (by rfl) hsh (by rroom)
  apply rx_swap1
  exact next

end seg

section memories

variable (rd : B256 → B256) (h i : B256) (M : Mem)

/-- The record's amount word. -/
abbrev amt : B256 := rd (2 + recordKey h i) >>> 64

/-- The memory after each of the record's writes. -/
def m1 : Mem := M.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes
def m2 : Mem := (m1 rd h i M).write (off1 i).toNat (rd (1 + recordKey h i)).toBytes
def m3 : Mem := (m2 rd h i M).write (off2 i).toNat (keyMask &&& rd (2 + recordKey h i)).toBytes
def m4 : Mem := (m3 rd h i M).write ((7 : B256) + amountAt i).toNat [(amt rd h i >>> 56).2.2.toUInt8]
def m5 : Mem := (m4 rd h i M).write ((6 : B256) + amountAt i).toNat [(amt rd h i >>> 48).2.2.toUInt8]
def m6 : Mem := (m5 rd h i M).write ((5 : B256) + amountAt i).toNat [(amt rd h i >>> 40).2.2.toUInt8]
def m7 : Mem := (m6 rd h i M).write ((4 : B256) + amountAt i).toNat [(amt rd h i >>> 32).2.2.toUInt8]
def m8 : Mem := (m7 rd h i M).write ((3 : B256) + amountAt i).toNat [(amt rd h i >>> 24).2.2.toUInt8]
def m9 : Mem := (m8 rd h i M).write ((2 : B256) + amountAt i).toNat [(amt rd h i >>> 16).2.2.toUInt8]
def m10 : Mem := (m9 rd h i M).write ((1 : B256) + amountAt i).toNat [(amt rd h i >>> 8).2.2.toUInt8]
def m11 : Mem := (m10 rd h i M).write (amountAt i).toNat [(amt rd h i).2.2.toUInt8]

/-- A record's memory charges, write by write. -/
theorem recordStage_gas :
    MemoryStage.selectedGas (recordStage rd h i) M =
      chg M (off0 i) 32 + chg (m1 rd h i M) (off1 i) 32 + chg (m2 rd h i M) (off2 i) 32 +
      chg (m3 rd h i M) ((7 : B256) + amountAt i) 1 + chg (m4 rd h i M) ((6 : B256) + amountAt i) 1 +
      chg (m5 rd h i M) ((5 : B256) + amountAt i) 1 + chg (m6 rd h i M) ((4 : B256) + amountAt i) 1 +
      chg (m7 rd h i M) ((3 : B256) + amountAt i) 1 + chg (m8 rd h i M) ((2 : B256) + amountAt i) 1 +
      chg (m9 rd h i M) ((1 : B256) + amountAt i) 1 + chg (m10 rd h i M) (amountAt i) 1 := by
  simp only [recordStage, MemoryStage.selectedGas, B256.length_toBytes, List.length_cons,
    List.length_nil, Nat.zero_add, chg, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, amt]
  omega

theorem recordStage_apply : (recordStage rd h i).applyMemory M = m11 rd h i M := by
  simp only [recordStage, MemoryStage.applyMemory, List.foldl, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2,
    m1]

end memories

theorem entry6 : cert.prog[6]? = some (sysHeader sysShape t_00e9_c1) := rfl

/-- **One exact iteration of the certified drain**, ending on the loop's back-edge. Any storage, any
memory. -/
theorem body_run {sevm : Sevm} {b : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (next : SFunc.RunExact cert.prog sevm
      (St (readsBase sevm b (recordKeys h i)) [(1 : B256) + i, c, h, t]
        ((recordStage (b.getStorVal sevm.currentTarget) h i).applyMemory M) gas)
      (sysHeader sysShape t_00e9_c1) oc) :
    SFunc.RunExact cert.prog sevm
      (St b [i, c, h, t] M (gas + 255 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage (b.getStorVal sevm.currentTarget) h i) M)) t_00e9_c1 oc := by
  generalize hrd : b.getStorVal sevm.currentTarget = rd at next ⊢
  have hv : ∀ k, b.getStorVal sevm.currentTarget k = rd k := fun k => by rw [hrd]
  rw [recordStage_apply] at next
  have hreads : readsBase sevm b (recordKeys h i) =
      afterSloadA sevm (afterSloadA sevm (afterSloadA sevm b (recordKey h i)) (1 + recordKey h i))
        (2 + recordKey h i) := rfl
  rw [hreads] at next
  generalize hr1 : afterSloadA sevm b (recordKey h i) = r1 at next
  generalize hr2 : afterSloadA sevm r1 (1 + recordKey h i) = r2 at next
  generalize hr3 : afterSloadA sevm r2 (2 + recordKey h i) = r3 at next
  have tail : SFunc.RunExact cert.prog sevm (St r3 [i, c, h, t] (m11 rd h i M) (gas + 17))
      (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.push [0xe1] (by decide))
        (.jump 6)))) oc := by
    have e : gas + 17 = gas + 8 + 3 + 3 + 3 := by omega
    rw [e]
    apply rx_push (w := (1 : B256)) (by decide) (by rroom)
    apply rx_add' rfl (by rroom)
    apply rx_push rfl (by rroom)
    exact rx_jump entry6 next
  have low : SFunc.RunExact cert.prog sevm
      (St r3 (amountAt i :: amt rd h i :: [i, c, h, t]) (m10 rd h i M)
        (gas + 17 + chg (m10 rd h i M) (amountAt i) 1))
      (.next (.reg .mstore8) (.next (.push [0x01] (by decide)) (.next (.reg .add)
        (.next (.push [0xe1] (by decide)) (.jump 6))))) oc := by
    apply rx_mstore8 (Devm.extCost_add_of_size rfl rfl) rfl
    exact tail
  have y1 := seg_byte (s := 0x08) (n := 0x01) (sn := 8) (nv := 1) (M := m9 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) low
  have y2 := seg_byte (s := 0x10) (n := 0x02) (sn := 16) (nv := 2) (M := m8 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y1
  have y3 := seg_byte (s := 0x18) (n := 0x03) (sn := 24) (nv := 3) (M := m7 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y2
  have y4 := seg_byte (s := 0x20) (n := 0x04) (sn := 32) (nv := 4) (M := m6 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y3
  have y5 := seg_byte (s := 0x28) (n := 0x05) (sn := 40) (nv := 5) (M := m5 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y4
  have y6 := seg_byte (s := 0x30) (n := 0x06) (sn := 48) (nv := 6) (M := m4 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y5
  have y7 := seg_byte (s := 0x38) (n := 0x07) (sn := 56) (nv := 7) (M := m3 rd h i M) (b := r3)
    (p := amountAt i) (a := amt rd h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y6
  have r2eq : r2.getStorVal sevm.currentTarget (2 + recordKey h i) = rd (2 + recordKey h i) := by
    rw [← hr2, ← hr1]
    simp only [afterSloadA_getStorVal, hv]
  have pk := seg_packed (M := m2 rd h i M) (b := r2) (o := off2 i) (key := recordKey h i)
    (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) (le3 := by decide) (le4 := by decide)
    hacc hsh (by rroom) r2eq (by rw [hr3]; exact y7)
  have r1eq : r1.getStorVal sevm.currentTarget (1 + recordKey h i) = rd (1 + recordKey h i) := by
    rw [← hr1]
    simp only [afterSloadA_getStorVal, hv]
  have w1 := seg_word (k := 0x01) (kv := 1) (M := m1 rd h i M) (b := r1) (o := off1 i)
    (key := recordKey h i) (T := [i, c, h, t]) (le1 := by decide) (le2 := by decide) hacc (by decide)
    (by rroom) r1eq (by rw [hr2]; exact pk)
  have w0 := seg_source (M := M) (b := b) (o := off0 i) (key := recordKey h i) (T := [i, c, h, t])
    (le1 := by decide) (le2 := by decide) hacc hsh (by rroom) (hv _) (by rw [hr1]; exact w1)
  have st := seg_start (w := 0x03) (wv := 3) (l := 0x4c) (lv := 76) (i := i) (c := c) (h := h) (t := t)
    (le1 := by decide) (le2 := by decide) (le3 := by decide) (by decide) (by decide) w0
  have e : ∀ g, gas + 255 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M = g →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M g) t_00e9_c1 oc →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M (gas + 255 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M)) t_00e9_c1 oc := fun _ hg r => hg ▸ r
  refine e _ ?_ st
  rw [recordStage_gas]
  subst hr3 hr2 hr1
  simp only [readsGas, recordKeys]
  omega

/-- The runtime's system path. -/
def sysPath : SysPath where
  code := withdrawalRequestCode
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape := sysShape
  systemDest := ⟨0xcb, [], by decide⟩
  user := t_001a_c0
  body := t_00e9_c1
  capN := 16
  cap_word := by decide
  slots := 3
  writes := 11
  bodyFixed := 255
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

variable {i : Nat} (hi : i < 16)
include hi

theorem off0_nat : (off0 i.toB256).toNat = 76 * i :=
  (mul_toB256_toNat_of_lt (a := 76) (n := i) (by omega) (by
    rw [show (76 : B256).toNat = 76 by decide]
    omega)).trans (by rw [show (76 : B256).toNat = 76 by decide])

theorem off1_nat : (off1 i.toB256).toNat = 20 + 76 * i :=
  lit_add_toNat (by decide) (off0_nat hi) (by omega)

theorem off2_nat : (off2 i.toB256).toNat = 52 + 76 * i :=
  (lit_add_toNat (n := 32) (by decide) (off1_nat hi) (by omega)).trans (by omega)

theorem amountAt_nat : (amountAt i.toB256).toNat = 68 + 76 * i :=
  (lit_add_toNat (n := 16) (by decide) (off2_nat hi) (by omega)).trans (by omega)

/-- A record's writes at their actual offsets. -/
theorem recordStage_eq (rd : B256 → B256) (h : B256) :
    let key := recordKey h i.toB256
    let a := rd (2 + key) >>> 64
    recordStage rd h i.toB256 =
      [(76 * i, (rd key <<< 96).toBytes),
       (20 + 76 * i, (rd (1 + key)).toBytes),
       (52 + 76 * i, (keyMask &&& rd (2 + key)).toBytes),
       (75 + 76 * i, [(a >>> 56).2.2.toUInt8]),
       (74 + 76 * i, [(a >>> 48).2.2.toUInt8]),
       (73 + 76 * i, [(a >>> 40).2.2.toUInt8]),
       (72 + 76 * i, [(a >>> 32).2.2.toUInt8]),
       (71 + 76 * i, [(a >>> 24).2.2.toUInt8]),
       (70 + 76 * i, [(a >>> 16).2.2.toUInt8]),
       (69 + 76 * i, [(a >>> 8).2.2.toUInt8]),
       (68 + 76 * i, [a.2.2.toUInt8])] := by
  intro key a
  have hb : ∀ (l : B256) (n m : Nat), l.toNat = n → n ≤ 7 → n + 68 = m →
      (l + amountAt i.toB256).toNat = m + 76 * i := fun l n m hl hn hm =>
    (lit_add_toNat hl (amountAt_nat hi) (by omega)).trans (by omega)
  simp only [recordStage]
  rw [off0_nat hi, off1_nat hi, off2_nat hi, hb 7 7 75 (by decide) (by decide) rfl,
    hb 6 6 74 (by decide) (by decide) rfl, hb 5 5 73 (by decide) (by decide) rfl,
    hb 4 4 72 (by decide) (by decide) rfl, hb 3 3 71 (by decide) (by decide) rfl,
    hb 2 2 70 (by decide) (by decide) rfl, hb 1 1 69 (by decide) (by decide) rfl,
    amountAt_nat hi]

end offsets

/-- The allocation: 16 records of 76 bytes and the third word's 8 bytes past the last, rounded up. -/
def sysMemory : SysMemory sysPath where
  alloc := 1248
  aligned := by decide
  lenN := 76
  len_word := by decide
  len_le := by decide
  windows := fun rd h i hi w hw => by
    have hi' : i < 16 := hi
    show w.1 + w.2 ≤ 1248
    change w ∈ MemoryStage.footprint (recordStage rd h i.toB256) at hw
    rw [recordStage_eq hi' rd h] at hw
    simp only [MemoryStage.footprint, List.map_cons, List.map_nil, B256.length_toBytes,
      List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only <;> omega
  alloc_lt := by decide

/-- The bound on the system call's execution gas, from the rule record: 16 records of three reads and
eleven writes, four more reads, four stores, the allocation's expansion. The state gas is separate: it
draws on the reservoir. -/
theorem frameBound_le : sysPath.frameBound sysMemory.alloc ≤ 163000 := by decide

/-- The runtime's system call facts. -/
def sysCall : SysCall sysPath where
  memory := sysMemory
  target := withdrawalRequestPredeployAddress
  bound := 163000
  nonempty := by decide +kernel
  size_ne := by decide +kernel
  not_precompile := by decide
  bound_le := frameBound_le
  room := by decide

/-- **The EIP-7002 system call succeeds under Amsterdam, from any storage.** With the canonical code
installed, the checked system call returns, its post state is `sysState`, and it uses at most 163,000 of
its 30,000,000 gas. There is no storage premise. -/
theorem system_call_ok {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode) :
    ∃ out, processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
        .ok (sysState sysShape benv.state withdrawalRequestPredeployAddress, out) ∧
      systemTransactionGas - out.gasLeft ≤ 163000 :=
  let h := sysCall.spec hfork installed
  ⟨_, h.1, h.2⟩

end Blanc.Lift.WithdrawalRequest.Amsterdam
