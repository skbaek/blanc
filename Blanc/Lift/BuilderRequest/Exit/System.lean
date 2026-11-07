import Blanc.Lift.BuilderRequest.SystemPath
import Blanc.Lift.BuilderRequest.Exit.Jumps

/-!
# The exit runtime's system path

The runtime as an instance of `SysPath`: cap 16, target 2, three slots and 68 returned bytes per record.
The record body reads three words and writes three overlapping windows: the source address's word
shifted to the top, then the two public-key words 20 and 52 bytes in. Any storage, any memory.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

/-- The exit runtime's pushed words. -/
def sysShape : SysShape where
  under := ⟨0xf5, [], by decide⟩
  cap := ⟨0x10, [], by decide⟩
  post := ⟨0x01, [0x2d], by decide⟩
  emptied := ⟨0x01, [0x3f], by decide⟩
  excess := ⟨0x01, [0x4a], by decide⟩
  latch := ⟨0x01, [0x98], by decide⟩
  noCarry := ⟨0x01, [0x86], by decide⟩
  carry := ⟨0x01, [0x8e], by decide⟩
  final := ⟨0x01, [0xba], by decide⟩
  target := ⟨0x02, [], by decide⟩
  len := ⟨0x44, [], by decide⟩

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
  have hstage : ∀ M' : Mem, MemoryStage.selectedGas (recordStage rd h i) M' =
      gVerylow + (calculateMemoryGasCost (memExtSize M'.size (off0 i).toNat 32) -
          calculateMemoryGasCost M'.size) +
        (gVerylow + (calculateMemoryGasCost
            (memExtSize (M'.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes).size
              (off1 i).toNat 32) -
          calculateMemoryGasCost (M'.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes).size) +
        (gVerylow + (calculateMemoryGasCost
            (memExtSize ((M'.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes).write
                (off1 i).toNat (rd (1 + recordKey h i)).toBytes).size (off2 i).toNat 32) -
          calculateMemoryGasCost ((M'.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes).write
                (off1 i).toNat (rd (1 + recordKey h i)).toBytes).size) + 0)) := by
    intro M'
    simp only [recordStage, MemoryStage.selectedGas, B256.length_toBytes]
  rw [hstage]
  have happly : (recordStage rd h i).applyMemory M =
      ((M.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes).write
        (off1 i).toNat (rd (1 + recordKey h i)).toBytes).write
        (off2 i).toNat (rd (2 + recordKey h i)).toBytes := by
    simp only [recordStage, MemoryStage.applyMemory, List.foldl]
  rw [happly] at next
  simp only [readsGas, recordKeys, Nat.add_zero]
  generalize hg1 : gVerylow + (calculateMemoryGasCost (memExtSize M.size (off0 i).toNat 32) -
      calculateMemoryGasCost M.size) = c1
  generalize hM1 : M.write (off0 i).toNat (rd (recordKey h i) <<< 96).toBytes = M1 at next ⊢
  generalize hg2 : gVerylow + (calculateMemoryGasCost (memExtSize M1.size (off1 i).toNat 32) -
      calculateMemoryGasCost M1.size) = c2
  generalize hM2 : M1.write (off1 i).toNat (rd (1 + recordKey h i)).toBytes = M2 at next ⊢
  generalize hg3 : gVerylow + (calculateMemoryGasCost (memExtSize M2.size (off2 i).toNat 32) -
      calculateMemoryGasCost M2.size) = c3
  have e : gas + 99 + (sloadCost sevm b (recordKey h i) +
        (sloadCost sevm (afterSloadA sevm b (recordKey h i)) (1 + recordKey h i) +
        sloadCost sevm (afterSloadA sevm (afterSloadA sevm b (recordKey h i)) (1 + recordKey h i))
          (2 + recordKey h i))) + (c1 + (c2 + c3)) =
      gas + 8 + 3 + 3 + 3 + c3 + 3 +
        sloadCost sevm (afterSloadA sevm (afterSloadA sevm b (recordKey h i)) (1 + recordKey h i))
          (2 + recordKey h i) + 3 + 3 + 3 + 3 + 3 + c2 + 3 +
        sloadCost sevm (afterSloadA sevm b (recordKey h i)) (1 + recordKey h i) + 3 + 3 + 3 + 3 + 3 +
        c1 + 3 + 3 + 3 + sloadCost sevm b (recordKey h i) + 3 + 5 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 := by
    omega
  rw [e]
  unfold t_00ff_c2
  refine rx_dup3 (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
  refine rx_mul rfl (by rroom) ?_
  refine rx_push (w := (4 : B256)) (by decide) (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_push (w := (68 : B256)) (by decide) (by rroom) ?_
  refine rx_mul rfl (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_sloadV hacc (by rroom) (hv _) ?_
  refine rx_push (w := (96 : B256)) (by decide) (by rroom) ?_
  refine rx_shl (v := rd (recordKey h i) <<< 96) (by rfl) hsh (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_mstore (M' := M1) (Devm.extCost_add_of_size rfl hg1) hM1 ?_
  refine rx_push (w := (20 : B256)) (by decide) (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_sloadV (v := rd (1 + recordKey h i)) hacc (by rroom)
    ((afterSloadA_getStorVal _ _ _ _ _).trans (hv _)) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_mstore (M' := M2) (Devm.extCost_add_of_size rfl hg2) hM2 ?_
  refine rx_push (w := (32 : B256)) (by decide) (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_swap1 ?_
  refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_sloadV (v := rd (2 + recordKey h i)) hacc (by rroom)
    ((afterSloadA_getStorVal _ _ _ _ _).trans
      ((afterSloadA_getStorVal _ _ _ _ _).trans (hv _))) ?_
  refine rx_swap1 ?_
  refine rx_mstore (Devm.extCost_add_of_size rfl hg3) rfl ?_
  refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  exact rx_jump entry7 next

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
  entry2 := rfl
  entry3 := rfl
  entry4 := rfl
  entry5 := rfl
  body_run := fun hacc hsh next => body_run hacc hsh next

end Blanc.Lift.BuilderRequest.Exit
