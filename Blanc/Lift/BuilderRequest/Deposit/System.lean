import Blanc.Lift.BuilderRequest.SystemPath
import Blanc.Lift.RequestSystem.BodySegs
import Blanc.Lift.BuilderRequest.Deposit.Jumps

/-!
# The deposit runtime's system path

The runtime as an instance of `SysPath`: cap 64, target 8, six slots and 184 returned bytes per record.
The record body reads six words and writes fourteen windows: three words, the amount's eight bytes
little-endian over the third word, three more words. Any storage, any memory.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem

/-- The deposit runtime's pushed words. -/
def sysWords : LatchWords where
  latch := ⟨0x02, [0x42], by decide⟩
  noCarry := ⟨0x02, [0x30], by decide⟩
  carry := ⟨0x02, [0x38], by decide⟩
  final := ⟨0x02, [0x64], by decide⟩
  target := ⟨0x08, [], by decide⟩
  len := ⟨0xb8, [], by decide⟩

/-- The deposit runtime's pushed words, as a system-path shape. -/
def sysShape : SysShape :=
  latchShape sysWords ⟨0x01, [0x31], by decide⟩ ⟨0x40, [], by decide⟩ ⟨0x01, [0xd7], by decide⟩
    ⟨0x01, [0xe9], by decide⟩ ⟨0x01, [0xf4], by decide⟩

/-! ## Segments of the certified body -/

section seg

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome} {M : Mem} {G : Nat}

/-- `DUP2 PUSH1 2 ADD SLOAD DUP1 DUP3 MSTORE PUSH1 0x40 SHR PUSH8 mask AND`: the packed word, stored
whole, with its amount split out. -/
theorem seg_packed {o key mask v : B256} {T : List B256} {xs : Bytes} {x : UInt8} {le1 le2 le3}
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (hsh : sevm.benvStat.rules.op.shifts = true) (hmask : Bytes.toB256 (x :: xs) = mask)
    (hroom : T.length ≤ 1000) (hv : b.getStorVal sevm.currentTarget ((2 : B256) + key) = v)
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b ((2 : B256) + key)) ((mask &&& (v >>> 64)) :: o :: key :: T)
        (M.write o.toNat v.toBytes) G) f oc) :
    SFunc.RunExact fs sevm
      (St b (o :: key :: T) M (G + 27 + chg M o 32 + sloadCost sevm b ((2 : B256) + key)))
      (.next (.reg (.dup 1)) (.next (.push [0x02] le1) (.next (.reg .add) (.next (.reg .sload)
        (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .mstore)
          (.next (.push [0x40] le2) (.next (.reg .shr) (.next (.push (x :: xs) le3)
            (.next (.reg .and) f))))))))))) oc := by
  have e : G + 27 + chg M o 32 + sloadCost sevm b ((2 : B256) + key) =
      G + 3 + 3 + 3 + 3 + chg M o 32 + 3 + 3 + sloadCost sevm b ((2 : B256) + key) + 3 + 3 + 3 := by
    omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_push (w := (2 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  apply rx_sloadV hacc (by rroom) hv
  apply rx_dup1 (by rroom)
  apply rx_dup3 (by rroom)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (64 : B256)) (by decide) (by rroom)
  apply rx_shr (v := v >>> 64) (by rfl) hsh (by rroom)
  apply rx_push hmask (by rroom)
  apply rx_and rfl (by rroom)
  exact next

/-- `MSTORE8 PUSH1 0x20 ADD`: the amount's low byte, then the next word's offset. -/
theorem seg_low {p a o key : B256} {T : List B256} {le}
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm
      (St b (((32 : B256) + o) :: key :: T) (M.write p.toNat [a.2.2.toUInt8]) G) f oc) :
    SFunc.RunExact fs sevm (St b (p :: a :: o :: key :: T) M (G + 6 + chg M p 1))
      (.next (.reg .mstore8) (.next (.push [0x20] le) (.next (.reg .add) f))) oc := by
  have e : G + 6 + chg M p 1 = G + 3 + 3 + chg M p 1 := by omega
  rw [e]
  apply rx_mstore8 (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push (w := (32 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

/-- `DUP2 PUSH1 0x10 ADD`: the amount's byte pointer. -/
theorem seg_ptr {o a : B256} {T : List B256} {le}
    (hroom : T.length ≤ 1000)
    (next : SFunc.RunExact fs sevm (St b (((16 : B256) + o) :: a :: o :: T) M G) f oc) :
    SFunc.RunExact fs sevm (St b (a :: o :: T) M (G + 9))
      (.next (.reg (.dup 1)) (.next (.push [0x10] le) (.next (.reg .add) f))) oc := by
  have e : G + 9 = G + 3 + 3 + 3 := by omega
  rw [e]
  apply rx_dup2 (by rroom)
  apply rx_push (w := (16 : B256)) (by decide) (by rroom)
  apply rx_add' rfl (by rroom)
  exact next

end seg

/-! ## One record -/

/-- A record's first storage key. -/
def recordKey (h i : B256) : B256 := (4 : B256) + (6 : B256) * (i + h)

/-- The keys a record's body reads. -/
def recordKeys (h i : B256) : List B256 :=
  [recordKey h i, 1 + recordKey h i, 2 + recordKey h i, 3 + recordKey h i, 4 + recordKey h i,
    5 + recordKey h i]

/-- The memory offsets, from the record's index. -/
def off0 (i : B256) : B256 := (184 : B256) * i
def off1 (i : B256) : B256 := 32 + off0 i
def off2 (i : B256) : B256 := 32 + off1 i
def amountAt (i : B256) : B256 := 16 + off2 i
def off3 (i : B256) : B256 := 32 + off2 i
def off4 (i : B256) : B256 := 32 + off3 i
def off5 (i : B256) : B256 := 32 + off4 i

/-- The amount: bits 64 to 127 of the record's third word. -/
def amountOf (w2 : B256) : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& (w2 >>> 64)

/-- A record's fourteen memory writes, in execution order. -/
def recordStage (rd : B256 → B256) (h i : B256) : MemoryStage :=
  let key := recordKey h i
  let a := amountOf (rd (2 + key))
  [((off0 i).toNat, (rd key).toBytes),
   ((off1 i).toNat, (rd (1 + key)).toBytes),
   ((off2 i).toNat, (rd (2 + key)).toBytes),
   (((7 : B256) + amountAt i).toNat, [(a >>> 56).2.2.toUInt8]),
   (((6 : B256) + amountAt i).toNat, [(a >>> 48).2.2.toUInt8]),
   (((5 : B256) + amountAt i).toNat, [(a >>> 40).2.2.toUInt8]),
   (((4 : B256) + amountAt i).toNat, [(a >>> 32).2.2.toUInt8]),
   (((3 : B256) + amountAt i).toNat, [(a >>> 24).2.2.toUInt8]),
   (((2 : B256) + amountAt i).toNat, [(a >>> 16).2.2.toUInt8]),
   (((1 : B256) + amountAt i).toNat, [(a >>> 8).2.2.toUInt8]),
   ((amountAt i).toNat, [a.2.2.toUInt8]),
   ((off3 i).toNat, (rd (3 + key)).toBytes),
   ((off4 i).toNat, (rd (4 + key)).toBytes),
   ((off5 i).toNat, (rd (5 + key)).toBytes)]

section memories

variable (rd : B256 → B256) (h i : B256) (M : Mem)

/-- The memory after each of the record's writes. -/
def m1 : Mem := M.write (off0 i).toNat (rd (recordKey h i)).toBytes
def m2 : Mem := (m1 rd h i M).write (off1 i).toNat (rd (1 + recordKey h i)).toBytes
def m3 : Mem := (m2 rd h i M).write (off2 i).toNat (rd (2 + recordKey h i)).toBytes
/-- The record's amount. -/
abbrev amt : B256 := amountOf (rd (2 + recordKey h i))
def m4 : Mem := (m3 rd h i M).write ((7 : B256) + amountAt i).toNat [(amt rd h i >>> 56).2.2.toUInt8]
def m5 : Mem := (m4 rd h i M).write ((6 : B256) + amountAt i).toNat [(amt rd h i >>> 48).2.2.toUInt8]
def m6 : Mem := (m5 rd h i M).write ((5 : B256) + amountAt i).toNat [(amt rd h i >>> 40).2.2.toUInt8]
def m7 : Mem := (m6 rd h i M).write ((4 : B256) + amountAt i).toNat [(amt rd h i >>> 32).2.2.toUInt8]
def m8 : Mem := (m7 rd h i M).write ((3 : B256) + amountAt i).toNat [(amt rd h i >>> 24).2.2.toUInt8]
def m9 : Mem := (m8 rd h i M).write ((2 : B256) + amountAt i).toNat [(amt rd h i >>> 16).2.2.toUInt8]
def m10 : Mem := (m9 rd h i M).write ((1 : B256) + amountAt i).toNat [(amt rd h i >>> 8).2.2.toUInt8]
def m11 : Mem := (m10 rd h i M).write (amountAt i).toNat [(amt rd h i).2.2.toUInt8]
def m12 : Mem := (m11 rd h i M).write (off3 i).toNat (rd (3 + recordKey h i)).toBytes
def m13 : Mem := (m12 rd h i M).write (off4 i).toNat (rd (4 + recordKey h i)).toBytes
def m14 : Mem := (m13 rd h i M).write (off5 i).toNat (rd (5 + recordKey h i)).toBytes

/-- A record's memory charges, write by write. -/
theorem recordStage_gas :
    MemoryStage.selectedGas (recordStage rd h i) M =
      chg M (off0 i) 32 + chg (m1 rd h i M) (off1 i) 32 + chg (m2 rd h i M) (off2 i) 32 +
      chg (m3 rd h i M) ((7 : B256) + amountAt i) 1 + chg (m4 rd h i M) ((6 : B256) + amountAt i) 1 +
      chg (m5 rd h i M) ((5 : B256) + amountAt i) 1 + chg (m6 rd h i M) ((4 : B256) + amountAt i) 1 +
      chg (m7 rd h i M) ((3 : B256) + amountAt i) 1 + chg (m8 rd h i M) ((2 : B256) + amountAt i) 1 +
      chg (m9 rd h i M) ((1 : B256) + amountAt i) 1 + chg (m10 rd h i M) (amountAt i) 1 +
      chg (m11 rd h i M) (off3 i) 32 + chg (m12 rd h i M) (off4 i) 32 + chg (m13 rd h i M) (off5 i) 32 := by
  simp only [recordStage, MemoryStage.selectedGas, B256.length_toBytes, List.length_cons,
    List.length_nil, Nat.zero_add, chg, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, amt]
  omega

end memories

section reads

variable (sevm : Sevm) (b : Devm) (h i : B256)

/-- The base after each of the record's reads. -/
def r1 : Devm := afterSloadA sevm b (recordKey h i)
def r2 : Devm := afterSloadA sevm (r1 sevm b h i) (1 + recordKey h i)
def r3 : Devm := afterSloadA sevm (r2 sevm b h i) (2 + recordKey h i)
def r4 : Devm := afterSloadA sevm (r3 sevm b h i) (3 + recordKey h i)
def r5 : Devm := afterSloadA sevm (r4 sevm b h i) (4 + recordKey h i)

theorem readsBase_recordKeys :
    readsBase sevm b (recordKeys h i) = afterSloadA sevm (r5 sevm b h i) (5 + recordKey h i) := rfl

end reads

theorem recordStage_apply (rd : B256 → B256) (h i : B256) (M : Mem) :
    (recordStage rd h i).applyMemory M = m14 rd h i M := by
  simp only [recordStage, MemoryStage.applyMemory, List.foldl, m14, m13, m12, m11, m10, m9, m8, m7, m6,
    m5, m4, m3, m2, m1]

theorem entry7 : cert.prog[7]? = some (sysHeader sysShape t_013b_c2) := rfl

/-- **One exact iteration of the certified drain**, ending on the loop's back-edge. Any storage, any
memory. -/
theorem body_run {sevm : Sevm} {b : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (next : SFunc.RunExact cert.prog sevm
      (St (readsBase sevm b (recordKeys h i)) [(1 : B256) + i, c, h, t]
        ((recordStage (b.getStorVal sevm.currentTarget) h i).applyMemory M) gas)
      (sysHeader sysShape t_013b_c2) oc) :
    SFunc.RunExact cert.prog sevm
      (St b [i, c, h, t] M (gas + 297 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage (b.getStorVal sevm.currentTarget) h i) M)) t_013b_c2 oc := by
  generalize hrd : b.getStorVal sevm.currentTarget = rd at next ⊢
  rw [recordStage_apply, readsBase_recordKeys] at next
  have hv : ∀ k, b.getStorVal sevm.currentTarget k = rd k := fun k => by rw [hrd]
  have s17 : SFunc.RunExact cert.prog sevm
      (St (afterSloadA sevm (r5 sevm b h i) (5 + recordKey h i)) [i, c, h, t] (m14 rd h i M) (gas + 17))
      (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.push [0x01, 0x33] (by decide))
        (.jump 7)))) oc := by
    have e : gas + 17 = gas + 8 + 3 + 3 + 3 := by omega
    rw [e]
    apply rx_push (w := (1 : B256)) (by decide) (by rroom)
    apply rx_add' rfl (by rroom)
    apply rx_push rfl (by rroom)
    exact rx_jump entry7 next
  have s5 := seg_last (k := 0x05) (kv := 5) (M := m13 rd h i M) (b := r5 sevm b h i) (o := off5 i) (key := recordKey h i) (T := [i, c, h, t]) (v := rd (5 + recordKey h i))
    (le := by decide) hacc (by decide) (by rroom) (by simp only [r5, r4, r3, r2, r1, afterSloadA_getStorVal, hv]) s17
  have s4 := seg_word (k := 0x04) (kv := 4) (M := m12 rd h i M) (b := r4 sevm b h i) (o := off4 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (4 + recordKey h i)) (le1 := by decide) (le2 := by decide) hacc (by decide) (by rroom)
    (by simp only [r4, r3, r2, r1, afterSloadA_getStorVal, hv]) s5
  have s3 := seg_word (k := 0x03) (kv := 3) (M := m11 rd h i M) (b := r3 sevm b h i) (o := off3 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (3 + recordKey h i)) (le1 := by decide) (le2 := by decide) hacc (by decide) (by rroom)
    (by simp only [r3, r2, r1, afterSloadA_getStorVal, hv]) s4
  have low := seg_low (M := m10 rd h i M) (b := r3 sevm b h i) (p := amountAt i) (a := amt rd h i) (o := off2 i) (key := recordKey h i)
    (T := [i, c, h, t]) (le := by decide) (by rroom) s3
  have y1 := seg_byte (s := 0x08) (n := 0x01) (sn := 8) (nv := 1) (M := m9 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) low
  have y2 := seg_byte (s := 0x10) (n := 0x02) (sn := 16) (nv := 2) (M := m8 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y1
  have y3 := seg_byte (s := 0x18) (n := 0x03) (sn := 24) (nv := 3) (M := m7 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y2
  have y4 := seg_byte (s := 0x20) (n := 0x04) (sn := 32) (nv := 4) (M := m6 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y3
  have y5 := seg_byte (s := 0x28) (n := 0x05) (sn := 40) (nv := 5) (M := m5 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y4
  have y6 := seg_byte (s := 0x30) (n := 0x06) (sn := 48) (nv := 6) (M := m4 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y5
  have y7 := seg_byte (s := 0x38) (n := 0x07) (sn := 56) (nv := 7) (M := m3 rd h i M) (b := r3 sevm b h i)
    (p := amountAt i) (a := amt rd h i) (T := off2 i :: recordKey h i :: [i, c, h, t]) (le1 := by decide) (le2 := by decide) hsh
    (by decide) (by decide) (by rroom) y6
  have ptr := seg_ptr (M := m3 rd h i M) (b := r3 sevm b h i) (o := off2 i) (a := amt rd h i) (T := recordKey h i :: [i, c, h, t])
    (le := by decide) (by rroom) y7
  have pk := seg_packed (M := m2 rd h i M) (b := r2 sevm b h i) (o := off2 i) (key := recordKey h i)
    (mask := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) (T := [i, c, h, t]) (x := 0xff)
    (xs := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) (v := rd (2 + recordKey h i))
    (le1 := by decide) (le2 := by decide) (le3 := by decide) hacc hsh rfl (by rroom)
    (by simp only [r2, r1, afterSloadA_getStorVal, hv]) ptr
  have w1 := seg_word (k := 0x01) (kv := 1) (M := m1 rd h i M) (b := r1 sevm b h i) (o := off1 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (1 + recordKey h i)) (le1 := by decide) (le2 := by decide) hacc (by decide) (by rroom)
    (by simp only [r1, afterSloadA_getStorVal, hv]) pk
  have w0 := seg_word0 (M := M) (b := b) (o := off0 i) (key := recordKey h i) (T := [i, c, h, t]) (v := rd (recordKey h i))
    (le2 := by decide) hacc (by rroom) (hv _) w1
  have st := seg_start (w := 0x06) (wv := 6) (l := 0xb8) (lv := 184) (i := i) (c := c) (h := h) (t := t)
    (le1 := by decide) (le2 := by decide) (le3 := by decide) (by decide) (by decide) w0
  have e : ∀ g, gas + 297 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M = g →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M g) t_013b_c2 oc →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M (gas + 297 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M)) t_013b_c2 oc := fun _ hg r => hg ▸ r
  refine e _ ?_ st
  rw [recordStage_gas]
  simp only [readsGas, recordKeys, r5, r4, r3, r2, r1]
  omega

/-- The deposit runtime's system path. -/
def sysPath : SysPath where
  code := code
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape := sysShape
  systemDest := ⟨0x01, [0x1c], by decide⟩
  user := t_001b_c0
  body := t_013b_c2
  capN := 64
  cap_word := by decide
  slots := 6
  writes := 14
  bodyFixed := 297
  keys := recordKeys
  keys_length := fun _ _ => rfl
  stage := recordStage
  stage_length := fun _ _ _ => rfl
  root := rfl
  entry := rfl
  excessEntry := rfl
  excess_run := fun hacc hpush0 hdata next => excess_run sysWords hacc hpush0 hdata rfl rfl next
  body_run := fun hacc hsh next => body_run hacc hsh next

end Blanc.Lift.BuilderRequest.Deposit
