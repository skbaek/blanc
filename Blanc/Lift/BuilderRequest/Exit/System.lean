import Blanc.Lift.BuilderRequest.SystemPath
import Blanc.Lift.RequestSystem.BodySegs
import Blanc.Lift.BuilderRequest.Exit.Jumps

/-!
# The exit runtime's system path

The runtime as an instance of `SysPath`: cap 16, target 2, three slots and 68 returned bytes per record.
The record body reads three words and writes three overlapping windows: the source address's word
shifted to the top, then the two public-key words 20 and 52 bytes in. Any storage, any memory.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem

/-- The exit runtime's pushed words. -/
def sysWords : LatchWords where
  latch := ⟨0x01, [0x98], by decide⟩
  noCarry := ⟨0x01, [0x86], by decide⟩
  carry := ⟨0x01, [0x8e], by decide⟩
  final := ⟨0x01, [0xba], by decide⟩
  target := ⟨0x02, [], by decide⟩
  len := ⟨0x44, [], by decide⟩

/-- The exit runtime's pushed words, as a system-path shape. -/
def sysShape : SysShape :=
  latchShape sysWords ⟨0xf5, [], by decide⟩ ⟨0x10, [], by decide⟩ ⟨0x01, [0x2d], by decide⟩
    ⟨0x01, [0x3f], by decide⟩ ⟨0x01, [0x4a], by decide⟩

/-- A record's first storage key. -/
def recordKey (h i : B256) : B256 := (4 : B256) + (3 : B256) * (i + h)

/-- The keys a record's body reads. -/
def recordKeys (h i : B256) : List B256 :=
  [recordKey h i, 1 + recordKey h i, 2 + recordKey h i]

/-- The memory offsets, from the record's index. -/
def off0 (i : B256) : B256 := (68 : B256) * i
def off1 (i : B256) : B256 := 20 + off0 i
def off2 (i : B256) : B256 := 32 + off1 i

/-- A record's three memory writes, in execution order. -/
def recordStage (rd : B256 → B256) (h i : B256) : MemoryStage :=
  [((off0 i).toNat, (rd (recordKey h i) <<< 96).toBytes),
   ((off1 i).toNat, (rd (1 + recordKey h i)).toBytes),
   ((off2 i).toNat, (rd (2 + recordKey h i)).toBytes)]

theorem readsBase_recordKeys (sevm : Sevm) (b : Devm) (h i : B256) :
    readsBase sevm b (recordKeys h i) =
      afterSloadA sevm (afterSloadA sevm (afterSloadA sevm b (recordKey h i)) (1 + recordKey h i))
        (2 + recordKey h i) := rfl

theorem entry7 : cert.prog[7]? = some (sysHeader sysShape t_00ff_c2) := rfl

/-- **One exact iteration of the certified drain**, ending on the loop's back-edge. Any storage, any
memory. -/
theorem body_run {sevm : Sevm} {b : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (next : SFunc.RunExact cert.prog sevm
      (St (readsBase sevm b (recordKeys h i)) [(1 : B256) + i, c, h, t]
        ((recordStage (b.getStorVal sevm.currentTarget) h i).applyMemory M) gas)
      (sysHeader sysShape t_00ff_c2) oc) :
    SFunc.RunExact cert.prog sevm
      (St b [i, c, h, t] M (gas + 99 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage (b.getStorVal sevm.currentTarget) h i) M)) t_00ff_c2 oc := by
  generalize hrd : b.getStorVal sevm.currentTarget = rd at next ⊢
  have hv : ∀ k, b.getStorVal sevm.currentTarget k = rd k := fun k => by rw [hrd]
  rw [readsBase_recordKeys] at next
  generalize hr1 : afterSloadA sevm b (recordKey h i) = r1 at next
  generalize hr2 : afterSloadA sevm r1 (1 + recordKey h i) = r2 at next
  generalize hM1 : M.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes = M1
  generalize hM2 : M1.write (off1 i).toNat (rd (1 + recordKey h i)).toBytes = M2
  have happly : (recordStage rd h i).applyMemory M =
      M2.write (off2 i).toNat (rd (2 + recordKey h i)).toBytes := by
    subst hM2 hM1
    simp only [recordStage, MemoryStage.applyMemory, List.foldl]
  rw [happly] at next
  have hgas : MemoryStage.selectedGas (recordStage rd h i) M =
      chg M (off0 i) 32 + chg M1 (off1 i) 32 + chg M2 (off2 i) 32 := by
    subst hM2 hM1
    simp only [recordStage, MemoryStage.selectedGas, B256.length_toBytes, chg]
    omega
  have tail : SFunc.RunExact cert.prog sevm
      (St (afterSloadA sevm r2 (2 + recordKey h i)) [i, c, h, t]
        (M2.write (off2 i).toNat (rd (2 + recordKey h i)).toBytes) (gas + 17))
      (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.push [0xf7] (by decide))
        (.jump 7)))) oc := by
    have e : gas + 17 = gas + 8 + 3 + 3 + 3 := by omega
    rw [e]
    apply rx_push (w := (1 : B256)) (by decide) (by rroom)
    apply rx_add' rfl (by rroom)
    apply rx_push rfl (by rroom)
    exact rx_jump entry7 next
  have s2 := seg_last (k := 0x02) (kv := 2) (M := M2) (b := r2) (o := off2 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (2 + recordKey h i)) (le := by decide) hacc (by decide) (by rroom)
    (by subst hr2 hr1; simp only [afterSloadA_getStorVal, hv]) tail
  have s1 := seg_word (k := 0x01) (kv := 1) (M := M1) (b := r1) (o := off1 i) (key := recordKey h i)
    (T := [i, c, h, t]) (v := rd (1 + recordKey h i)) (le1 := by decide) (le2 := by decide) hacc
    (by decide) (by rroom) (by subst hr1; simp only [afterSloadA_getStorVal, hv])
    (by rw [hr2, hM2]; exact s2)
  have s0 := seg_source (M := M) (b := b) (o := off0 i) (key := recordKey h i) (T := [i, c, h, t])
    (le1 := by decide) (le2 := by decide) hacc hsh (by rroom) (hv _) (by rw [hr1, hM1]; exact s1)
  have st := seg_start (w := 0x03) (wv := 3) (l := 0x44) (lv := 68) (i := i) (c := c) (h := h) (t := t)
    (le1 := by decide) (le2 := by decide) (le3 := by decide) (by decide) (by decide) s0
  have e : ∀ g, gas + 99 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M = g →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M g) t_00ff_c2 oc →
      SFunc.RunExact cert.prog sevm (St b [i, c, h, t] M (gas + 99 + readsGas sevm b (recordKeys h i) +
        MemoryStage.selectedGas (recordStage rd h i) M)) t_00ff_c2 oc := fun _ hg r => hg ▸ r
  refine e _ ?_ st
  rw [hgas]
  subst hr2 hr1
  simp only [readsGas, recordKeys]
  omega

/-- The exit runtime's system path. -/
def sysPath : SysPath where
  code := code
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape := sysShape
  systemDest := ⟨0xe1, [], by decide⟩
  user := t_001a_c0
  body := t_00ff_c2
  capN := 16
  cap_word := by decide
  slots := 3
  writes := 3
  bodyFixed := 99
  keys := recordKeys
  keys_length := fun _ _ => rfl
  stage := recordStage
  stage_length := fun _ _ _ => rfl
  root := rfl
  entry := rfl
  excessEntry := rfl
  excess_run := fun hacc hpush0 hdata next => excess_run sysWords hacc hpush0 hdata rfl rfl next
  body_run := fun hacc hsh next => body_run hacc hsh next

end Blanc.Lift.BuilderRequest.Exit
