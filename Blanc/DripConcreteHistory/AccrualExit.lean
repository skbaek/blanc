import Blanc.DripConcreteHistory.Accrual

namespace Blanc
open Jaune
namespace Drip

private theorem concreteDrip_stage (sevm : Sevm) (base post : Devm) (G : Nat)
    (hfresh : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripStagingMemory, G, base.stateGas⟩) freshStart post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 27, base.stateGas⟩) drip post := by
  func_run (3) [6]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], concreteDripStagingMemory, G + 27 - 15, base.stateGas⟩) (.call freshStartSlot) post
  apply Func.runCompiled_call' (f := freshStart) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hfresh

private theorem concreteDrip_square (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (next : Func) (hsize : M.size = 288)
    (hread : Bytes.toB256 (M.read (baseWord * 32).toNat 32).1 = rate)
    (hmem : (M.read (baseWord * 32).toNat 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write (baseWord * 32).toNat concreteDripSquare.toBytes, G, base.stateGas⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 107, base.stateGas⟩)
      (guardedRoundedMul baseWord baseWord baseWord next) post := by
  unfold guardedRoundedMul roundedMulRecovery
  rw [if_pos rfl]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hread, hmem]
  func_run (11) [rate * rate, rate, 1, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  func_run (8) [half + rate * rate, 0]
  func_run (1)
  func_run (5) [concreteDripSquare, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write (baseWord * 32).toNat concreteDripSquare.toBytes, G + 107 - 107, base.stateGas⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_accumulate (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (next : Func) (hsize : M.size = 288)
    (hacc : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = rate)
    (haccMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hbase : Bytes.toB256 (M.read (baseWord * 32).toNat 32).1 = concreteDripSquare)
    (hbaseMem : (M.read (baseWord * 32).toNat 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write (accumulatorWord * 32).toNat concreteDripFactor.toBytes, G, base.stateGas⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 110, base.stateGas⟩)
      (guardedRoundedMul accumulatorWord baseWord accumulatorWord next) post := by
  unfold guardedRoundedMul roundedMulRecovery
  rw [if_neg (by decide +kernel)]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hacc, haccMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase, hbaseMem]
  func_run (4) [rate * concreteDripSquare, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase, hbaseMem]
  func_run (4) [rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hacc, haccMem]
  func_run (2) [1, 0]
  func_run (8) [half + rate * concreteDripSquare, 0]
  func_run (1)
  func_run (5) [concreteDripFactor, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write (accumulatorWord * 32).toNat concreteDripFactor.toBytes, G + 110 - 110, base.stateGas⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_loopOne (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hexp : Bytes.toB256 (M.read 0 32).1 = 1) (hexpMem : (M.read 0 32).2 = M)
    (hbase : Bytes.toB256 (M.read 224 32).1 = rate) (hbaseMem : (M.read 224 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write 224 concreteDripSquare.toBytes, G, base.stateGas⟩) rpowAfterSquare post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 140, base.stateGas⟩) rpowLoop post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[Bytes.toB256 (M.read 0 32).1], (M.read 0 32).2, G + 140 - 5, base.stateGas⟩) _ post
  rw [hexp, hexpMem]
  func_run (2) [0]
  rw [show G + 140 - 21 = (G + 12) + 107 by omega]
  apply concreteDrip_square _ _ _ _ _ _ hsize hbase hbaseMem
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write 224 concreteDripSquare.toBytes, G + 12, base.stateGas⟩) (.call rpowAfterSquareSlot) post
  apply Func.runCompiled_call' (f := rpowAfterSquare) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using htail

private theorem concreteDrip_afterSquare (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hexp : Bytes.toB256 (M.read 0 32).1 = 1) (hexpMem : (M.read 0 32).2 = M)
    (hacc : Bytes.toB256 (M.read 256 32).1 = rate) (haccMem : (M.read 256 32).2 = M)
    (hbase : Bytes.toB256 (M.read 224 32).1 = concreteDripSquare)
    (hbaseMem : (M.read 224 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write 256 concreteDripFactor.toBytes, G, base.stateGas⟩) rpowAdvance post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 147, base.stateGas⟩) rpowAfterSquare post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[Bytes.toB256 (M.read 0 32).1], (M.read 0 32).2, G + 147 - 5, base.stateGas⟩) _ post
  rw [hexp, hexpMem]
  func_run (3) [1]
  rw [show G + 147 - 25 = (G + 12) + 110 by omega]
  apply concreteDrip_accumulate _ _ _ _ _ _ hsize hacc haccMem hbase hbaseMem
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write 256 concreteDripFactor.toBytes, G + 12, base.stateGas⟩) (.call rpowAdvanceSlot) post
  apply Func.runCompiled_call' (f := rpowAdvance) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using htail

private theorem concreteDrip_advance (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hexp : Bytes.toB256 (M.read 0 32).1 = 1) (hexpMem : (M.read 0 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write 0 (0 : B256).toBytes, G, base.stateGas⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 33, base.stateGas⟩) rpowAdvance post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[Bytes.toB256 (M.read 0 32).1], (M.read 0 32).2, G + 33 - 5, base.stateGas⟩) _ post
  rw [hexp, hexpMem]
  func_run (5) [0, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write 0 (0 : B256).toBytes, G + 33 - 21, base.stateGas⟩) (.call rpowLoopSlot) post
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using htail

private theorem concreteDrip_rpowZero (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hread : Bytes.toB256 (M.read 0 32).1 = 0)
    (hmem : (M.read 0 32).2 = M)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G, base.stateGas⟩) composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 34, base.stateGas⟩) rpowLoop post := by
  func_run (1)
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of (v := 0) (M := M) (c := 3) (G := G + 29)
      (s := []) rfl ?_ hread hmem ?_ (by decide)) ?_
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  simp only [Devm.setMach_setMach]
  func_run (2) [1]
  apply Func.runCompiled_call' (f := composeFresh) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hcompose


def concreteDripSquareMemory : Mem := concreteDripLoopMemory.write 224 concreteDripSquare.toBytes
def concreteDripFactorMemory : Mem := concreteDripSquareMemory.write 256 concreteDripFactor.toBytes
def concreteDripRpowMemory : Mem := concreteDripFactorMemory.write 0 (0 : B256).toBytes

private def concreteDripLoopImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes)

private theorem concreteDrip_loopReads : Mem.Reads concreteDripLoopMemory concreteDripLoopImage := by
  unfold concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripLoopImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_loopSize : concreteDripLoopMemory.size = 288 := by decide +kernel

private theorem concreteDrip_loopUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripLoopMemory.read i 32).2 = concreteDripLoopMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_loopSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_loopRead0 :
    Bytes.toB256 (concreteDripLoopMemory.read 0 32).1 = (1 : B256) := by
  rw [concreteDrip_loopReads.read]
  unfold concreteDripLoopImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_loopRead224 :
    Bytes.toB256 (concreteDripLoopMemory.read 224 32).1 = rate := by
  rw [concreteDrip_loopReads.read]
  unfold concreteDripLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 224 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 224 256 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private def concreteDripSquareImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes) 224 concreteDripSquare.toBytes)

private theorem concreteDrip_squareReads : Mem.Reads concreteDripSquareMemory concreteDripSquareImage := by
  unfold concreteDripSquareMemory concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripSquareImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_squareSize : concreteDripSquareMemory.size = 288 := by
  unfold concreteDripSquareMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteDrip_loopSize]; decide)]
  exact concreteDrip_loopSize

private theorem concreteDrip_squareUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripSquareMemory.read i 32).2 = concreteDripSquareMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_squareSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_squareRead0 :
    Bytes.toB256 (concreteDripSquareMemory.read 0 32).1 = (1 : B256) := by
  rw [concreteDrip_squareReads.read]
  unfold concreteDripSquareImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 0 224 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_squareRead224 :
    Bytes.toB256 (concreteDripSquareMemory.read 224 32).1 = concreteDripSquare := by
  rw [concreteDrip_squareReads.read]
  unfold concreteDripSquareImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_squareRead256 :
    Bytes.toB256 (concreteDripSquareMemory.read 256 32).1 = rate := by
  rw [concreteDrip_squareReads.read]
  unfold concreteDripSquareImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private def concreteDripFactorImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes) 224 concreteDripSquare.toBytes) 256 concreteDripFactor.toBytes)

private theorem concreteDrip_factorReads : Mem.Reads concreteDripFactorMemory concreteDripFactorImage := by
  unfold concreteDripFactorMemory concreteDripSquareMemory concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripFactorImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_factorSize : concreteDripFactorMemory.size = 288 := by
  unfold concreteDripFactorMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteDrip_squareSize])]
  exact concreteDrip_squareSize

private theorem concreteDrip_factorUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripFactorMemory.read i 32).2 = concreteDripFactorMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_factorSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_factorRead0 :
    Bytes.toB256 (concreteDripFactorMemory.read 0 32).1 = (1 : B256) := by
  rw [concreteDrip_factorReads.read]
  unfold concreteDripFactorImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 0 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 0 224 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private def concreteDripRpowImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes) 224 concreteDripSquare.toBytes) 256 concreteDripFactor.toBytes) 0 (0 : B256).toBytes)

private theorem concreteDrip_rpowReads : Mem.Reads concreteDripRpowMemory concreteDripRpowImage := by
  unfold concreteDripRpowMemory concreteDripFactorMemory concreteDripSquareMemory concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripRpowImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_rpowSize : concreteDripRpowMemory.size = 288 := by
  unfold concreteDripRpowMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteDrip_factorSize]; decide)]
  exact concreteDrip_factorSize

private theorem concreteDrip_rpowUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripRpowMemory.read i 32).2 = concreteDripRpowMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_rpowSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_rpowRead0 :
    Bytes.toB256 (concreteDripRpowMemory.read 0 32).1 = (0 : B256) := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead32 :
    Bytes.toB256 (concreteDripRpowMemory.read 32 32).1 = (4 : B256) := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead160 :
    Bytes.toB256 (concreteDripRpowMemory.read 160 32).1 = rate := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 192 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead192 :
    Bytes.toB256 (concreteDripRpowMemory.read 192 32).1 = (5 : B256) := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead256 :
    Bytes.toB256 (concreteDripRpowMemory.read 256 32).1 = concreteDripFactor := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _


theorem concreteDrip_rpow (sevm : Sevm) (base post : Devm) (G : Nat)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripRpowMemory, G, base.stateGas⟩) composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripLoopMemory, G + 354, base.stateGas⟩) rpowLoop post := by
  rw [show G + 354 = (G + 214) + 140 by omega]
  apply concreteDrip_loopOne
  · exact concreteDrip_loopSize
  · exact concreteDrip_loopRead0
  · exact concreteDrip_loopUnchanged _ (by decide)
  · exact concreteDrip_loopRead224
  · exact concreteDrip_loopUnchanged _ (by decide)
  change Func.RunCompiled _ sevm (base.setMach ⟨[], concreteDripSquareMemory, G + 214, base.stateGas⟩) rpowAfterSquare post
  rw [show G + 214 = (G + 67) + 147 by omega]
  apply concreteDrip_afterSquare
  · exact concreteDrip_squareSize
  · exact concreteDrip_squareRead0
  · exact concreteDrip_squareUnchanged _ (by decide)
  · exact concreteDrip_squareRead256
  · exact concreteDrip_squareUnchanged _ (by decide)
  · exact concreteDrip_squareRead224
  · exact concreteDrip_squareUnchanged _ (by decide)
  change Func.RunCompiled _ sevm (base.setMach ⟨[], concreteDripFactorMemory, G + 67, base.stateGas⟩) rpowAdvance post
  rw [show G + 67 = (G + 34) + 33 by omega]
  apply concreteDrip_advance
  · exact concreteDrip_factorSize
  · exact concreteDrip_factorRead0
  · exact concreteDrip_factorUnchanged _ (by decide)
  exact concreteDrip_rpowZero _ _ _ _ _ concreteDrip_rpowSize concreteDrip_rpowRead0
    (concreteDrip_rpowUnchanged _ (by decide)) hcompose

private theorem concreteDrip_composeFresh (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hchi : Bytes.toB256 (M.read (storedChiWord * 32).toNat 32).1 = rate)
    (hchiMem : (M.read (storedChiWord * 32).toNat 32).2 = M)
    (hfactor : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = concreteDripFactor)
    (hfactorMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hroute : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G, base.stateGas⟩) freshRoute post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 104, base.stateGas⟩) composeFresh post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [rate * concreteDripFactor, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (3) [1, 0]
  func_run (7) [concreteDripChi, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  apply Func.runCompiled_call' (f := freshRoute) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hroute

private theorem concreteDrip_freshRoute (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hroute : Bytes.toB256 (M.read (routeWord * 32).toNat 32).1 = routeDrip)
    (hmem : (M.read (routeWord * 32).toNat 32).2 = M)
    (hdrip : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G, base.stateGas⟩) afterDrip post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G + 97, base.stateGas⟩) freshRoute post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hroute, hmem]
  func_run (17) [0, 0, 0, 1]
  simpa only [Nat.add_sub_cancel] using hdrip


private theorem concreteDrip_afterDrip (sevm : Sevm) (base C R : Devm) (M : Mem) (G : Nat)
    (hstatic : sevm.isStatic = false) (hfork : CoveredFork sevm.benvStat.fork) (hsize : M.size = 288)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 5)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hchiCost : sstoreCost sevm base chiSlot concreteDripChi = 2900)
    (hchi : afterSstore sevm base chiSlot concreteDripChi = C)
    (hrhoCost : sstoreCost sevm C rhoSlot 5 = 2900)
    (hrho : afterSstore sevm C rhoSlot 5 = R) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G + 5825, base.stateGas⟩) afterDrip
      ((R.setMach ⟨[], M.write 0 concreteDripChi.toBytes, G, R.stateGas⟩).withOutput concreteDripChi.toBytes) := by
  have hCStateGas : C.stateGas = base.stateGas := by
    rw [← hchi]
    unfold afterSstore
    split <;> rfl
  have hRStateGas : R.stateGas = C.stateGas := by
    rw [← hrho]
    unfold afterSstore
    split <;> rfl
  rw [hRStateGas]
  func_run (2)
  rw [show G + 5825 - 6 = (G + 2919) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := C.setMach ⟨[concreteDripChi], M, G + 2919, base.stateGas⟩) ?_ ?_
  · simpa only [hchiCost, hchi] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := base)
        (key := chiSlot) (value := concreteDripChi) (stack := [concreteDripChi])
        (memory := M) (G := G + 2919) hfork
        (by rw [hchiCost]; simp only [gCallStipend]; omega) hstatic)
  rw [← hCStateGas]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (1)
  rw [show G + 2919 - 9 = (G + 10) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := R.setMach ⟨[concreteDripChi], M, G + 10, C.stateGas⟩) ?_ ?_
  · simpa only [hrhoCost, hrho] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := C)
        (key := rhoSlot) (value := 5) (stack := [concreteDripChi])
        (memory := M) (G := G + 10) hfork
        (by rw [hrhoCost]; simp only [gCallStipend]; omega) hstatic)
  func_run (4) [0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  have hnsize : (M.write 0 concreteDripChi.toBytes).size = 288 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
    exact hsize
  have hnread : ((M.write 0 concreteDripChi.toBytes).read 0 32).1 = concreteDripChi.toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M (ys := concreteDripChi.toBytes) (by decide +kernel))
  have hnmem : ((M.write 0 concreteDripChi.toBytes).read 0 32).2 = M.write 0 concreteDripChi.toBytes := by
    apply Mem.read_snd_eq_self
    rw [hnsize]
    decide +kernel
  apply Func.runCompiled_return_of (G := G) (e := 0)
  · rfl
  · change calculateMemoryGasCost (memExtsSize (M.write 0 concreteDripChi.toBytes).size [(0, 32)]) -
      calculateMemoryGasCost (M.write 0 concreteDripChi.toBytes).size = 0
    rw [hnsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  · change (((M.write 0 concreteDripChi.toBytes).read 0 32).1,
      R.setMach ⟨[], ((M.write 0 concreteDripChi.toBytes).read 0 32).2, G, C.stateGas⟩) = _
    rw [hnread, hnmem]


noncomputable def concreteDripStorageBase : Devm := concreteDripFreshBase concreteDripSevm concreteDripDevm
noncomputable def concreteDripChiBase : Devm :=
  (concreteDripStorageBase.withRefundCounter 0).setStorVal concreteCreateTarget chiSlot concreteDripChi
noncomputable def concreteDripRhoBase : Devm :=
  (concreteDripChiBase.withRefundCounter 0).setStorVal concreteCreateTarget rhoSlot 5

private theorem concreteDrip_originalStorage (key : B256) :
    getOrigStorVal concreteDripSevm concreteCreateTarget key =
      (concreteJoined.state.getStor concreteCreateTarget).get key := by rfl

private theorem concreteDripStorageBase_warm (key : B256) (hk : key = chiSlot ∨ key = rhoSlot) :
    (concreteCreateTarget, key) ∈ concreteDripStorageBase.accessedStorageKeys := by
  change (concreteCreateTarget, key) ∈ (concreteDripDevm.accessedStorageKeys.insert
    (concreteCreateTarget, chiSlot)).insert (concreteCreateTarget, rhoSlot)
  rcases hk with rfl | rfl <;> simp

private theorem concreteDrip_chiStore :
    sstoreCost concreteDripSevm concreteDripStorageBase chiSlot concreteDripChi = 2900 ∧
    afterSstore concreteDripSevm concreteDripStorageBase chiSlot concreteDripChi = concreteDripChiBase := by
  have ht : concreteDripSevm.currentTarget = concreteCreateTarget := rfl
  have hw := concreteDripStorageBase_warm chiSlot (Or.inl rfl)
  have hr : concreteDripStorageBase.refundCounter = 0 := rfl
  have hv : concreteDripStorageBase.getStorVal concreteCreateTarget chiSlot = rate := concreteDripDevm_chi
  have hc : sstoreValueCost rate rate concreteDripChi = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteDripSevm.benvStat.rules.gas concreteDripChi rate rate 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteDrip_originalStorage,
      concreteJoined_values.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteDrip_originalStorage,
      concreteJoined_values.1, hv, hr, hf]
    rfl

private theorem concreteDrip_rhoStore :
    sstoreCost concreteDripSevm concreteDripChiBase rhoSlot 5 = 2900 ∧
    afterSstore concreteDripSevm concreteDripChiBase rhoSlot 5 = concreteDripRhoBase := by
  have ht : concreteDripSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, rhoSlot) ∈ concreteDripChiBase.accessedStorageKeys := by
    rw [concreteDripChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteDripStorageBase_warm rhoSlot (Or.inr rfl)
  have hr : concreteDripChiBase.refundCounter = 0 := rfl
  have hv : concreteDripChiBase.getStorVal concreteCreateTarget rhoSlot = 2 := by
    change (Devm.getStor ((concreteDripStorageBase.withRefundCounter 0).setStorVal
      concreteCreateTarget chiSlot concreteDripChi) concreteCreateTarget).get rhoSlot = _
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteDripDevm_rho
  have hc : sstoreValueCost 2 2 5 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteDripSevm.benvStat.rules.gas 5 2 2 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteDrip_originalStorage,
      concreteJoined_values.2.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteDrip_originalStorage,
      concreteJoined_values.2.1, hv, hr, hf]
    rfl

noncomputable def concreteDripRuntimePost (G : Nat) : Devm :=
  (concreteDripRhoBase.setMach ⟨[], concreteDripRpowMemory.write 0 concreteDripChi.toBytes, G, concreteDripRhoBase.stateGas⟩).withOutput
    concreteDripChi.toBytes

theorem concreteDrip_endpoint (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteDripSevm
      (concreteDripDevm.setMach ⟨[], Mem.empty, G + 10877, concreteDripDevm.stateGas⟩) drip (concreteDripRuntimePost G) := by
  rw [show G + 10877 = G + 5825 + 97 + 104 + 354 + 122 + 2166 + 79 + 2103 + 27 by omega]
  apply concreteDrip_stage
  apply concreteDrip_freshStart
  · rfl
  · exact CoveredFork.prague.rules_stateGas_none
  · exact concreteDripDevm_chi
  · exact concreteDripDevm_rho
  · exact concreteDripDevm_cold _
  · exact concreteDripDevm_cold _
  apply concreteDrip_rpow
  apply concreteDrip_composeFresh
  · exact concreteDrip_rpowSize
  · exact concreteDrip_rpowRead160
  · exact concreteDrip_rpowUnchanged _ (by decide)
  · exact concreteDrip_rpowRead256
  · exact concreteDrip_rpowUnchanged _ (by decide)
  apply concreteDrip_freshRoute
  · exact concreteDrip_rpowSize
  · exact concreteDrip_rpowRead32
  · exact concreteDrip_rpowUnchanged _ (by decide)
  exact concreteDrip_afterDrip _ concreteDripStorageBase concreteDripChiBase concreteDripRhoBase _ G
    rfl CoveredFork.prague concreteDrip_rpowSize concreteDrip_rpowRead192 (concreteDrip_rpowUnchanged _ (by decide))
    concreteDrip_chiStore.1 concreteDrip_chiStore.2 concreteDrip_rhoStore.1 concreteDrip_rhoStore.2

private theorem concreteDrip_dispatch (sevm : Sevm) (base post : Devm) (G : Nat)
    (hdata : sevm.data = concreteDripTx.data)
    (hvalue : sevm.value = 0)
    (hdrip : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩) drip post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
    (base.setMach ⟨[], Mem.empty, G + 133, base.stateGas⟩) main post := by
  have hd : dripSelector = (0x9f678cca : B256) := by decide +kernel
  have hj : joinSelector = (0xb688a363 : B256) := by decide +kernel
  have hshift : Sevm.dataWord sevm 0 >>> B256.toNat 224 = dripSelector := by
    simp only [Sevm.dataWord, hdata, concreteDripTx]
    decide +kernel
  func_run (1)
  simp only [hdata, concreteDripTx]
  func_run (5) [dripSelector]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[dripSelector], Mem.empty, G + 133 - 27, base.stateGas⟩) (dispatch tree) post
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[dripSelector], Mem.empty, G + 133 - 27, base.stateGas⟩)
    (Ninst.dup 0 ::: Ninst.pushB256 dripSelector ::: Ninst.gt :::
      (dispatch (.fork (.fork (.leaf convertToAssetsSelector (nonpayable (exactCalldata 36 convertToAssets)))
          (.leaf exitSelector (nonpayable (exactCalldata 36 exit))))
        (.leaf convertToUnitsSelector (nonpayable (exactCalldata 36 convertToUnits)))) <?>
       dispatch (.fork (.leaf dripSelector (nonpayable (exactCalldata 4 drip)))
         (.leaf joinSelector (exactCalldata 4 join))))) post
  simp only [hd, hj]
  func_run (4) [0]
  func_run (4) [1]
  func_run (3) [1]
  func_run (1)
  rw [hvalue]
  func_run (2) [1]
  func_run (4) [1]
  all_goals first
    | simpa only [Nat.add_sub_cancel] using hdrip
    | (simp only [hdata, concreteDripTx]; decide +kernel)

theorem concreteDrip_runtime (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteDripSevm
      (concreteDripDevm.setMach ⟨[], Mem.empty, G + 11010, concreteDripDevm.stateGas⟩) main (concreteDripRuntimePost G) := by
  rw [show G + 11010 = (G + 10877) + 133 by omega]
  exact concreteDrip_dispatch _ _ _ _ rfl rfl (concreteDrip_endpoint G)

theorem concreteDripDevm_gas : concreteDripDevm.gasLeft = 478936 := by
  change 500000 - deploymentIntrinsicGas concreteDripTxInput concreteDripTx concreteCreateSender = 478936
  decide +kernel

theorem concreteDrip_program :
    Prog.RunCompiled concreteDripSevm concreteDripDevm runtime (concreteDripRuntimePost 467925) := by
  apply Prog.runCompiled_intro (G := 467925 + 11010)
    (mid := concreteDripDevm.setMach ⟨[], Mem.empty, 467925 + 11010, concreteDripDevm.stateGas⟩)
  · rw [concreteDripDevm_gas]
    decide
  · rfl
  exact concreteDrip_runtime 467925

theorem concreteDrip_compiled : some concreteDripSevm.code.toList = Prog.compile runtime := by
  change some concreteDripMessage.code.toList = _
  rw [concreteDripMessage_code, code_compile]

theorem concreteDrip_exec :
    exec (initEvm (concreteDripMessage.withBenv concreteDripEntry)) =
      .ok (concreteDripRuntimePost 467925) :=
  Prog.exec_of_runCompiled concreteDrip_program concreteDrip_compiled

theorem concreteDrip_frameEntry :
    (Frame.ofCall concreteDripMessage).enter =
      .run (initEvm (concreteDripMessage.withBenv concreteDripEntry)) := by
  have hnp : ¬ pragueRules.isPrecomp concreteCreateTarget :=
    concreteDeploymentBase.target_not_precompile (ChainConfig.pragueOnly_rulesAt 1 5)
  have he : executeCode.enter (concreteDripMessage.withBenv concreteDripEntry) =
      .inl (initEvm (concreteDripMessage.withBenv concreteDripEntry)) := by
    unfold executeCode.enter
    change (if !false && pragueRules.isPrecomp concreteCreateTarget then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, hnp]
    rfl
  unfold Frame.enter Frame.ofCall
  rw [concreteDripEntry_run]
  dsimp only
  rw [he]

private theorem concreteDrip_postError : (concreteDripRuntimePost 467925).error = none := rfl

theorem concreteDrip_processMessage :
    processMessage concreteDripMessage = .ok (concreteDripRuntimePost 467925) := by
  unfold processMessage runFrame
  rw [concreteDrip_frameEntry]
  simp [Frame.settle_eq_settleMsg_handleErrorWith, Frame.settleMsg, concreteDrip_exec,
    executeCode.handleErrorWith_ok, Frame.ofCall, processMessage.settle, concreteDrip_postError]

noncomputable def concreteDripMessageState : State := (concreteDripRuntimePost 467925).state

def concreteDripMessageOutput : MsgCallOutput := {
  gasLeft := 467925
  refundCounter := 0
  logs := []
  accountsToDelete := .emptyWithCapacity
  error := none
  returnData := concreteDripChi.toBytes }

theorem concreteDrip_messageCall :
    processMessageCall concreteDripMessage = .ok (concreteDripMessageState, concreteDripMessageOutput) := by
  have htarget : concreteDripMessage.target.isNone = false := rfl
  have hauths : concreteDripMessage.tenv.stat.auths = [] := rfl
  have hcode : some concreteDripMessage.code.toList = Prog.compile runtime := concreteDrip_compiled
  have hdelegation : getDelegatedCodeAddress concreteDripMessage.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcode)]
  have hrefund : (concreteDripRuntimePost 467925).refundCounter = 0 := rfl
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind, hdelegation,
    concreteDrip_processMessage, Except.bimap, id_eq, concreteDrip_postError,
    Option.isNone, hrefund]
  rfl

noncomputable def concreteDripTransactionState : State :=
  deploymentFinalState concreteDripTxInput concreteDripTx concreteCreateSender
    concreteDripMessageState 32075

def concreteDripTransactionBout : BlockOutput :=
  deploymentFinalBout .init concreteDripTx 0 concreteDripMessageOutput 32075

theorem concreteDrip_transaction :
    processTransaction concreteDripTxInput .init concreteDripTx 0 =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
  have hchecked := concreteDripChecked
  change checkTransaction concreteDripTxInput.beginTransaction
    (deploymentTxPreludeBout .init concreteDripTx 0) concreteDripTx =
      .ok (concreteCreateSender, 2, [], 0) at hchecked
  have hdebit := concreteDripDebit_run
  simp only [Benv.beginTransaction] at hdebit
  have hprepareRun :
      Except.bind
        (prepareMessage
          { concreteDripTxInput.beginTransaction with state := concreteDripDebit }
          concreteDripTenv concreteDripTx)
        (fun msg => Except.mapError TransitionError.vm (processMessageCall msg)) =
        .ok (concreteDripMessageState, concreteDripMessageOutput) := by
    rw [concreteDripMessage_prepared]
    simp only [Except.bind, concreteDrip_messageCall, Except.mapError]
  have hvalidationStateGas :
      concreteDripTxInput.beginTransaction.stat.rules.stateGas = none := by
    change concreteDripTxInput.stat.rules.stateGas = none
    exact CoveredFork.prague.rules_stateGas_none
  have hforkStateGas : pragueRules.stateGas = none := pragueRules_stateGas
  have hrules : concreteDripTxInput.beginTransaction.stat.rules = pragueRules := rfl
  have htypeThree : concreteDripTx.isTypeThree = false := rfl
  have haccessList : concreteDripTx.accessList = [] := rfl
  have hauths : concreteDripTx.auths = [] := rfl
  unfold processTransaction
  simp only [bind, Except.bind]
  change (do
    let validationSender ←
      ((match concreteDripTxInput.beginTransaction.stat.rules.stateGas with
        | none => Except.ok 0
        | some _ => do
          Except.mapError TransitionError.transaction
            (checkTransactionChainId concreteDripTxInput.beginTransaction concreteDripTx)
          Except.mapError (fun e => TransitionError.senderRecovery e)
            (recoverSender concreteDripTxInput.beginTransaction.stat.chainId concreteDripTx)) :
        Except TransitionError Adr)
    (fun _ => _) validationSender) =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) <;>
  rw [hvalidationStateGas]
  simp only [bind, Except.bind]
  rw [hrules]
  simp only [Except.mapError]
  simp only [deploymentTxPreludeBout, ExecutionTrace.transactionPreludeBout] at hchecked
  rw [hchecked]
  simp only [htypeThree, haccessList, hauths, Bool.false_eq_true, if_false,
    Nat.add_zero, Benv.beginTransaction]
  have htxGas : concreteDripTx.gas = 500000 := rfl
  rw [htxGas, show Nat.toB256 (500000 * 2) = 1000000 by decide +kernel, hdebit]
  simp only [Option.toExcept]
  change (Except.bind
    (Except.bind
      (prepareMessage
        {concreteDripTxInput.beginTransaction with state := concreteDripDebit}
        concreteDripTenv concreteDripTx)
      (fun msg => Except.mapError TransitionError.vm (processMessageCall msg)))
    (fun v => _)) = _
  rw [hprepareRun]
  simp only [Except.bind]
  have hprice : min 1 (8 - concreteDripTxInput.stat.baseFeePerGas) +
      concreteDripTxInput.stat.baseFeePerGas = 2 := by rfl
  have hgas : max (500000 - 467925 - min ((500000 - 467925) / 5) 0)
      (calculateIntrinsicCost pragueRules concreteDripTx concreteCreateSender).2 = 32075 := by decide +kernel
  unfold concreteDripMessageOutput
  rw [show Int.toNat? 0 = some 0 by rfl]
  simp only [hgas]
  unfold concreteDripTransactionState concreteDripTransactionBout deploymentFinalState deploymentFinalBout
  simp only [deploymentEffectiveGasPrice, concreteDripTx, concreteDripMessageOutput, hprice]
  have hdelete : (Std.HashSet.emptyWithCapacity : AdrSet).toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    rfl
  rw [hdelete]
  rfl


theorem concreteDripTransactionCode (a : Adr) :
    concreteDripTransactionState.getCode a = concreteJoined.state.getCode a := by
  unfold concreteDripTransactionState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode]
  unfold concreteDripMessageState concreteDripRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change concreteDripRhoBase.getCode a = _
  unfold concreteDripRhoBase
  rw [Devm.setStorVal_getCode]
  change concreteDripChiBase.getCode a = _
  unfold concreteDripChiBase
  rw [Devm.setStorVal_getCode]
  change concreteDripEntry.state.getCode a = _
  change ((concreteDripDebit.setBal _ _).addBal _ _).getCode a = _
  rw [State.addBal_getCode, State.setBal_getCode]
  unfold concreteDripDebit
  rw [State.setBal_getCode]
  change ((concreteJoined.state.incrNonce concreteCreateSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl

theorem concreteDrip_receiptEntry :
    concreteDripTransactionBout.receiptsTrie[deploymentReceiptKey 0]? =
      some (makeReceipt concreteDripTx none 32075 []) := by
  change (BlockOutput.init.receiptsTrie.insert (deploymentReceiptKey 0)
    (makeReceipt concreteDripTx none 32075 []))[deploymentReceiptKey 0]? = _
  rw [Std.TreeMap.getElem?_insert_self]

theorem concreteDrip_requestSuffix :
    processGeneralPurposeRequests (concreteDripTxInput.withState concreteDripTransactionState)
      concreteDripTransactionBout = .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
  have hcode (a : Adr) (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
      some (concreteDripTransactionState.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [concreteDripTransactionCode]
    rw [concreteJoinedCode]
    exact concreteDeployedSystemCode a ha
  obtain ⟨withdrawalOut, hw, _, _, _, _, hwr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (concreteDripTxInput.withState concreteDripTransactionState) withdrawalRequestPredeployAddress []
      (hcode _ (by simp)) (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
      CoveredFork.prague
  obtain ⟨consolidationOut, hc, _, _, _, _, hcr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((concreteDripTxInput.withState concreteDripTransactionState).withState concreteDripTransactionState)
      consolidationRequestPredeployAddress [] (hcode _ (by simp))
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide) CoveredFork.prague
  have hrequests :
      (concreteDripTxInput.withState concreteDripTransactionState).stat.rules.requests =
        [(1, withdrawalRequestPredeployAddress),
         (2, consolidationRequestPredeployAddress)] := by
    change pragueRules.requests = _
    exact pragueRules_requests
  have hw' : processCheckedSystemTransaction
      (concreteDripTxInput.withState concreteDripTransactionState)
      withdrawalRequestPredeployAddress [] =
      .ok (concreteDripTransactionState, withdrawalOut) := by
    simpa [Benv.withState] using hw
  have hbalNone :
      (concreteDripTxInput.withState concreteDripTransactionState).stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  have hbaseBalNone : concreteDripTxInput.stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  have hd : parseDepositRequests concreteDripTransactionBout = .ok [] := by
    unfold parseDepositRequests
    have hk : concreteDripTransactionBout.receiptKeys = [deploymentReceiptKey 0] := rfl
    rw [hk]
    simp
    rw [concreteDrip_receiptEntry]
    unfold makeReceipt
    rfl
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
  rw [hd, hrequests]
  simp [runRequestContracts, hw', hc, hwr, hcr, hbalNone, hbaseBalNone]
  rfl

theorem concreteDrip_body :
    applyBody concreteDripTxInput [.inl concreteDripTxRlp] [] =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
  obtain ⟨beaconOut, hb, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    concreteDripTxInput beaconRootsAddress concreteDripTxInput.stat.parentBeaconBlockRoot.toBytes
    (by change some (concreteJoined.state.getCode _).toList = _
        rw [concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp beaconRootsAddress; decide) CoveredFork.prague
  obtain ⟨historyOut, hh, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (concreteDripTxInput.withState concreteJoined.state) historyStorageAddress
    concreteJoinBlock.header.hash.toBytes
    (by change some (concreteJoined.state.getCode _).toList = _
        rw [concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp historyStorageAddress; decide) CoveredFork.prague
  have hl : (concreteDripTxInput.withState concreteJoined.state).stat.blockHashes.getLast? =
      some concreteJoinBlock.header.hash := by rfl
  have hi : (concreteDripTxInput.withState concreteJoined.state).withState concreteJoined.state =
      concreteDripTxInput := rfl
  have hstate : concreteDripTxInput.state = concreteJoined.state := rfl
  have hh' : processUncheckedSystemTransaction
      (concreteDripTxInput.withState concreteDripTxInput.state) historyStorageAddress
      concreteJoinBlock.header.hash.toBytes =
      .ok ((concreteDripTxInput.withState concreteDripTxInput.state).state, historyOut) := by
    simpa only [hstate] using hh
  have hl' : (concreteDripTxInput.withState concreteDripTxInput.state).stat.blockHashes.getLast? =
      some concreteJoinBlock.header.hash := by
    simpa only [hstate] using hl
  have hi' : (concreteDripTxInput.withState concreteDripTxInput.state).withState
      concreteDripTxInput.state = concreteDripTxInput := by
    simpa only [hstate] using hi
  have hbalNone : concreteDripTxInput.stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  unfold applyBody
  simp only [BalBuilder.incorporateSystem, hbalNone, checkBlockAccessListGasLimit]
  rw [hb]
  simp only [Except.mapError, bind, Except.bind]
  rw [hl']
  simp only [Option.toExcept, hh', Except.mapError, bind, Except.bind]
  rw [show (concreteDripTxInput.withState concreteDripTxInput.state).state =
    concreteDripTxInput.state from rfl, hi']
  have htransaction := concreteDrip_transaction
  unfold BlockOutput.init at htransaction
  simp only [BlockOutput.init, List.mapM_cons, List.mapM_nil, concreteDripDecode, pure, Except.pure, bind, Except.bind, List.putIndex, List.putIndex.aux,
    applyTransactions, htransaction]
  have hwithdrawals : processWithdrawals
      (concreteDripTxInput.withState concreteDripTransactionState)
      concreteDripTransactionBout [] =
      (concreteDripTransactionState, concreteDripTransactionBout) := by
    unfold processWithdrawals processWithdrawalsState processWithdrawalsTrie
      BlockOutput.withWithdrawalsTrie
    rfl
  rw [hwithdrawals]
  simp only [Prod.fst, Prod.snd]
  have hws (b : Benv) (st : State) : (b.withState st).withState st = b.withState st := rfl
  rw [hws]
  rw [concreteDrip_requestSuffix]
  rfl

noncomputable def concreteDripHeader (sr tr rr wr rh : B256) : Header :=
  { concreteDripExecutionHeader with
    gasUsed := 32075
    stateRoot := sr
    txsRoot := tr
    receiptRoot := rr
    withdrawalsRoot := wr
    requestsHash := some rh }

theorem concreteDripHeader_benv (sr tr rr wr rh : B256) :
    initBenv .prague concreteJoined (concreteDripHeader sr tr rr wr rh) = concreteDripTxInput := rfl

theorem concreteDripHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteJoined (concreteDripHeader sr tr rr wr rh) = .ok () := by
  have hlast : concreteJoined.blocks.getLast? = some concreteJoinBlock :=
    appendBlock_getLast? concreteDeployed.blocks concreteJoinBlock
  have hDeploy : concreteDeploymentEnvelope.block.header =
      concreteDeploymentHeader concreteDeploymentBody.1.root
        (getTransactionsRoot concreteDeploymentBody.2) (getReceiptRoot concreteDeploymentBody.2)
        (getWithdrawalsRoot concreteDeploymentBody.2)
        (computeRequestsHash concreteDeploymentBody.2.requests) := rfl
  have hJoin : concreteJoinBlock.header =
      concreteJoinHeader concreteJoinTransactionState.root
        (getTransactionsRoot concreteJoinTransactionBout) (getReceiptRoot concreteJoinTransactionBout)
        (getWithdrawalsRoot concreteJoinTransactionBout)
        (computeRequestsHash concreteJoinTransactionBout.requests) := rfl
  have hparentGasLimit : concreteJoinBlock.header.gasLimit = 10000000 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentGasUsed : concreteJoinBlock.header.gasUsed = 76144 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentBaseFee : concreteJoinBlock.header.baseFeePerGas = 1 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentTimestamp : concreteJoinBlock.header.timestamp = 2 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentNumber : concreteJoinBlock.header.number = 2 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentBlobGas : concreteJoinBlock.header.blobGasUsed = 0 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentExcessBlobGas : concreteJoinBlock.header.excessBlobGas = 0 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentExtraData : concreteJoinBlock.header.extraData = [] := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentDifficulty : concreteJoinBlock.header.difficulty = 0 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentNonce : concreteJoinBlock.header.nonce = 0 := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentOmmers : concreteJoinBlock.header.ommersHash = emptyOmmerHash := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentBal : concreteJoinBlock.header.blockAccessListHash = none := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentSlot : concreteJoinBlock.header.slotNumber = none := by
    simp only [hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hbase : calculateBaseFeePerGas 10000000 10000000 76144 1 = .ok 1 := by
    decide +kernel
  have hexcess : calculateExcessBlobGas pragueRules.blob concreteJoinBlock.header = 0 := by
    unfold calculateExcessBlobGas
    rw [hparentExcessBlobGas, hparentBlobGas]
    decide +kernel
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind,
    concreteDripHeader, concreteDripExecutionHeader, Header.hash, hparentGasLimit, hparentGasUsed, hparentBaseFee, hparentTimestamp, hparentNumber, hparentBlobGas, hparentExcessBlobGas, hparentExtraData, hparentDifficulty, hparentNonce, hparentOmmers, hparentBal, hparentSlot,
    hbase, hexcess, ne_eq, not_true_eq_false, ite_false]
  simp only [Except.mapError]
  rfl

noncomputable def concreteDripBlock : Block := {
  header := concreteDripHeader concreteDripTransactionState.root
    (getTransactionsRoot concreteDripTransactionBout) (getReceiptRoot concreteDripTransactionBout)
    (getWithdrawalsRoot concreteDripTransactionBout) (computeRequestsHash concreteDripTransactionBout.requests)
  txs := [.inl concreteDripTxRlp]
  ommers := []
  wds := [] }

noncomputable def concreteDripped : BlockChain :=
  ⟨appendBlock concreteJoined.blocks concreteDripBlock, concreteDripTransactionState, concreteJoined.chainId⟩

theorem concreteDrip_checks :
    stateTransitionChecks concreteDripTransactionBout concreteDripBlock.header
      (getTransactionsRoot concreteDripTransactionBout) concreteDripTransactionState.root
      (getReceiptRoot concreteDripTransactionBout) (logsBloom concreteDripTransactionBout.blockLogs)
      (getWithdrawalsRoot concreteDripTransactionBout)
      (computeRequestsHash concreteDripTransactionBout.requests) = .ok () := by
  have hg : concreteDripTransactionBout.blockGasUsed = 32075 := rfl
  have hl : concreteDripTransactionBout.blockLogs = [] := rfl
  have hb : concreteDripTransactionBout.blobGasUsed = 0 := rfl
  simp only [stateTransitionChecks, hg, hl, hb, concreteDripBlock, concreteDripHeader,
    concreteDripExecutionHeader, concreteJoinBlock, concreteJoinHeader, concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteDrip_step :
    stateTransitionUsing concreteConfig concreteJoined concreteDripBlock = .ok concreteDripped := by
  have hchain : concreteConfig.chainId = concreteJoined.chainId := concreteDeploymentRoot.deployed_chainId
  rw [stateTransitionUsing_eq_of_chainId_eq hchain]
  rw [show concreteConfig.forkAt concreteDripBlock.header.timestamp = .ok .prague from
    ChainConfig.pragueOnly_forkAt 1 _]
  change stateTransitionAt .prague concreteJoined concreteDripBlock = _
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE]
  have hh : validateHeader Fork.prague.ruleSet concreteJoined concreteDripBlock.header = .ok () := by
    change validateHeader pragueRules concreteJoined concreteDripBlock.header = .ok ()
    exact concreteDripHeader_valid _ _ _ _ _
  rw [hh]
  change (do
    let output ← applyBody (initBenv .prague concreteJoined concreteDripBlock.header)
      concreteDripBlock.txs concreteDripBlock.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteDripBlock.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs)
      (getWithdrawalsRoot output.2) (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteJoined.blocks concreteDripBlock, output.1,
      concreteJoined.chainId⟩ : BlockChain)) = .ok concreteDripped
  have hbody : applyBody (initBenv .prague concreteJoined concreteDripBlock.header)
      concreteDripBlock.txs concreteDripBlock.wds =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
    change applyBody (initBenv .prague concreteJoined (concreteDripHeader _ _ _ _ _))
      [.inl concreteDripTxRlp] [] = _
    rw [concreteDripHeader_benv]
    exact concreteDrip_body
  rw [hbody]
  simp only [Bind.bind, Except.bind, concreteDrip_checks, Except.mapError]
  rfl

theorem concreteDripped_storage : concreteDripped.state.getStor concreteCreateTarget =
    ((concreteJoined.state.getStor concreteCreateTarget).set chiSlot concreteDripChi).set rhoSlot 5 := by
  change concreteDripTransactionState.getStor concreteCreateTarget = _
  unfold concreteDripTransactionState deploymentFinalState State.getStor State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteDripMessageState concreteDripRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change Devm.getStor concreteDripRhoBase concreteCreateTarget = _
  unfold concreteDripRhoBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteDripChiBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  have hs : Devm.getStor concreteDripStorageBase concreteCreateTarget =
      (concreteJoined.state.get concreteCreateTarget).stor := by
    change (concreteDripEntry.state.get concreteCreateTarget).stor = _
    exact concreteDripEntry_storage _
  rw [hs]

theorem concreteDripped_values :
    (concreteDripped.state.getStor concreteCreateTarget).get chiSlot = concreteDripChi ∧
    (concreteDripped.state.getStor concreteCreateTarget).get rhoSlot = 5 ∧
    (concreteDripped.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 99 ∧
    (concreteDripped.state.getStor concreteCreateTarget).get totalUnitsSlot = 99 := by
  rw [concreteDripped_storage]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · exact Stor.get_set_self _ _ _
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel)]
    exact concreteJoined_values.2.2.1
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel)]
    exact concreteJoined_values.2.2.2

theorem concreteDrip_receiptSucceeded :
    (concreteDripTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true := by
  rw [concreteDrip_receiptEntry]
  rfl

theorem concreteDrip_observations :
    concreteDripMessageOutput.returnData = concreteDripChi.toBytes ∧
    concreteDripTransactionBout.blockGasUsed = 32075 ∧
    concreteDripTransactionBout.blockLogs = [] ∧
    concreteDripBlock.header.timestamp = 5 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem concreteDripMessageState_sender :
    concreteDripMessageState.get concreteCreateSender = concreteDripEntry.state.get concreteCreateSender := by
  unfold concreteDripMessageState concreteDripRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  change (((concreteDripEntry.state.setStorVal concreteCreateTarget chiSlot concreteDripChi).setStorVal
    concreteCreateTarget rhoSlot 5).get concreteCreateSender) = _
  simp only [State.setStorVal, State.get_set_ne _ ht]

theorem concreteDrippedSenderNonce : concreteDripped.state.getNonce concreteCreateSender = 3 := by
  change (concreteDripTransactionState.get concreteCreateSender).nonce = _
  unfold concreteDripTransactionState deploymentFinalState
  change (((concreteDripMessageState.addBal concreteCreateSender 935850).addBal 0 32075).get
    concreteCreateSender).nonce = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteDripMessageState_sender]
  change ((((concreteDripDebit.setBal concreteCreateSender
    (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateSender).nonce) = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  unfold concreteDripDebit
  simp only [State.setBal_get_self, State.incrNonce, State.get_set_self]
  change (concreteJoined.state.getNonce concreteCreateSender) + 1 = 3
  rw [concreteJoinedSenderNonce]
  rfl

theorem concreteDrippedSenderBalance : concreteDripped.state.bal concreteCreateSender = 999999999998823644 := by
  change (concreteDripTransactionState.get concreteCreateSender).bal = _
  unfold concreteDripTransactionState deploymentFinalState
  change (((concreteDripMessageState.addBal concreteCreateSender 935850).addBal 0 32075).get
    concreteCreateSender).bal = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  change (concreteDripMessageState.get concreteCreateSender).bal + 935850 = _
  rw [concreteDripMessageState_sender]
  change ((((concreteDripDebit.setBal concreteCreateSender
    (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateSender).bal) + 935850 = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  change (concreteDripDebit.bal concreteCreateSender - 0) + 935850 = _
  rw [concreteDripDebit_balance]
  decide +kernel

theorem concreteDrippedCode (a : Adr) :
    concreteDripped.state.getCode a = concreteJoined.state.getCode a := concreteDripTransactionCode a

def concreteExitTx : Tx := {
  nonce := 3
  gas := 500000
  value := 0
  data := [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
  v := 1
  r := (0x2c0058ac7e7b06e684ece60a8968d4fa9baee82b97db878467bc1637d680b80a : B256).toBytes
  s := (0x149ab14861a161a3b2c4448817f8031f3516a24cd5a55220aa471fc67063a424 : B256).toBytes
  type := .two 1 1 8 (some concreteCreateTarget) [] }

def concreteExitSigningPayload : Bytes :=
  [0x02, 0xf8, 0x44, 1, 3, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++
  concreteCreateTarget.toBytes ++ [0x80, 0xa4] ++ [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28] ++ [0xc0]

theorem concreteExitSigningEncoded :
    concreteExitTx.signingHash = some concreteExitSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 3).sig = [3] := by decide +kernel
  have ht : (BLT.bytes concreteCreateTarget.toBytes).toBytes =
      0x94 :: concreteCreateTarget.toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hlen : concreteCreateTarget.toBytes.length = 20 := rfl
  simp only [Tx.signingHash, concreteExitTx, hc, hn, AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list [.bytes [1], .bytes [3], .bytes (Nat.toBytes 1),
    .bytes (Nat.toBytes 8), .bytes (Nat.toBytes 500000), .bytes concreteCreateTarget.toBytes,
    .bytes (Nat.toBytes 0), .bytes [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28], .list []]).toBytes = _
  simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, ht, hlen,
    Nat.toBytes, Nat.toBytes.aux, concreteExitSigningPayload]
  rw [show Nat.toBytesPack 68 = [68] by decide +kernel]
  exact ⟨rfl, rfl⟩

theorem concreteExitSigningHash :
    concreteExitTx.signingHash =
      some (0x22c4bcb62ad0275fea1abcb8e2238dd2b59b0a62d83c953ed26e59ed645af53c : B256) := by
  rw [concreteExitSigningEncoded]
  decide +kernel

theorem concreteExitRecoveredSender :
    recoverSender 1 concreteExitTx = .ok concreteCreateSender := by
  rw [recoverSender, concreteExitSigningHash]
  decide +kernel

def concreteExitFields : List BLT :=
  [.bytes [1], .bytes [3], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
   .bytes concreteCreateTarget.toBytes, .bytes [], .bytes [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28],
   .list [], .bytes [1], .bytes concreteExitTx.r, .bytes concreteExitTx.s]

def concreteExitPayload : Bytes :=
  [1, 3, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++ concreteCreateTarget.toBytes ++
  [0x80, 0xa4] ++ [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28] ++ [0xc0, 1, 0xa0] ++ concreteExitTx.r ++
  [0xa0] ++ concreteExitTx.s

def concreteExitTxRlp : Bytes := [2, 0xf8, 0x87] ++ concreteExitPayload

theorem concreteExitBLT : concreteExitTx.toBLT = .list concreteExitFields := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 3).sig = [3] := by decide +kernel
  have hr : trimZero concreteExitTx.r = concreteExitTx.r := by decide +kernel
  have hs : trimZero concreteExitTx.s = concreteExitTx.s := by decide +kernel
  simp only [Tx.toBLT, concreteExitTx, hc, AccessList.toBLT, List.map_nil]
  simp [concreteExitFields, concreteExitTx, Nat.toBytes, Nat.toBytes.aux]
  exact ⟨hr, hs⟩

theorem concreteExitPayloadParse (k : Nat) :
    Bytes.toBLTs? (k + 12) concreteExitPayload = some concreteExitFields := by
  unfold concreteExitPayload concreteExitFields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 3 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 8 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [7, 0xa1, 0x20] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 36 [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k concreteExitTx.s [] rfl
  rw [Bytes.toBLTs?]

theorem concreteExitPayload_length : concreteExitPayload.length = 135 := by
  simp only [concreteExitPayload, List.length_append, List.length_cons, List.length_nil]
  rfl

theorem concreteExitEnvelopeParse :
    Bytes.toBLT? (0xf8 :: 0x87 :: concreteExitPayload) = some (.list concreteExitFields) := by
  have hsplit : Jaune.List.splitAt? 135 concreteExitPayload = some (concreteExitPayload, []) := by
    simpa only [concreteExitPayload_length, List.append_nil] using
      RlpConcrete.splitAt_append concreteExitPayload ([] : Bytes)
  have hp : Bytes.toBLTDiff? 137 (0xf8 :: 0x87 :: concreteExitPayload) =
      some (.list concreteExitFields, []) := by
    rw [Bytes.toBLTDiff?]
    change (do
      let p ← Jaune.List.splitAt? 1 ([0x87] ++ concreteExitPayload)
      let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
      let rs ← Bytes.toBLTs? 136 q.1
      pure (BLT.list rs, q.2)) = _
    rw [show Jaune.List.splitAt? 1 ([0x87] ++ concreteExitPayload) =
      some ([0x87], concreteExitPayload) from
        RlpConcrete.splitAt_append [0x87] concreteExitPayload]
    change (do
      let q ← Jaune.List.splitAt? 135 concreteExitPayload
      let rs ← Bytes.toBLTs? 136 q.1
      pure (BLT.list rs, q.2)) = _
    rw [hsplit]
    change (do let rs ← Bytes.toBLTs? 136 concreteExitPayload; pure (BLT.list rs, [])) = _
    rw [concreteExitPayloadParse 124]
    rfl
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteExitPayload_length]
  rw [hp]

theorem concreteExitDecode : decodeTx (.inl concreteExitTxRlp) = .ok concreteExitTx := by
  simp only [decodeTx, concreteExitTxRlp, List.cons_append, List.nil_append,
    Bytes.toExTx, concreteExitEnvelopeParse, concreteExitFields]
  rfl


noncomputable def concreteExitExecutionHeader : Header :=
  { concreteDripBlock.header with
    parentHash := concreteDripBlock.header.hash
    number := 4
    gasUsed := 0
    timestamp := 6 }

theorem concreteDrippedSenderCode : concreteDripped.state.getCode concreteCreateSender = ByteArray.empty := by
  rw [concreteDrippedCode]
  exact concreteJoinedSenderCode

theorem concreteExitSenderChecked :
    checkTransactionSenderAccount (concreteDripped.state.get concreteCreateSender)
      concreteExitTx 4000000 = .ok () := by
  have hn : (concreteDripped.state.get concreteCreateSender).nonce = 3 := concreteDrippedSenderNonce
  have hb : (concreteDripped.state.get concreteCreateSender).bal = 999999999998823644 :=
    concreteDrippedSenderBalance
  have hc : (concreteDripped.state.get concreteCreateSender).code = ByteArray.empty :=
    concreteDrippedSenderCode
  simp only [checkTransactionSenderAccount, hn, hb, checkTransactionSenderCode, hc]
  decide +kernel

theorem concreteExitValidated :
    validateTransaction pragueRules concreteExitTx 0 =
      .ok (calculateIntrinsicCost pragueRules concreteExitTx 0) := by
  decide +kernel

theorem concreteExitChecked :
    checkTransaction (initBenv .prague concreteDripped concreteExitExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteExitTx 0) concreteExitTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv .prague concreteDripped concreteExitExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteExitTx 0) concreteExitTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv .prague concreteDripped concreteExitExecutionHeader).beginTransaction
      concreteExitTx = .ok () := by decide +kernel
  have hfee : checkTransactionGasFee
      (initBenv .prague concreteDripped concreteExitExecutionHeader).beginTransaction
      concreteExitTx = .ok (2, 4000000) := by decide +kernel
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteExitTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv .prague concreteDripped concreteExitExecutionHeader).beginTransaction concreteExitTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv .prague concreteDripped concreteExitExecutionHeader).beginTransaction concreteExitTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteExitTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteExitTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteDripped.state.get sender) concreteExitTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteExitRecoveredSender, hfee]
  change (do
    Except.mapError TransitionError.transaction
      (checkTransactionSenderAccount (concreteDripped.state.get concreteCreateSender) concreteExitTx 4000000)
    pure (concreteCreateSender, 2, [], 0)) = _
  rw [concreteExitSenderChecked]
  rfl

noncomputable def concreteExitTxInput : Benv :=
  initBenv .prague concreteDripped concreteExitExecutionHeader

noncomputable def concreteExitDebit : State :=
  let nonceState := concreteDripped.state.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

theorem concreteExitDebit_run :
    (concreteExitTxInput.beginTransaction.state.incrNonce concreteCreateSender).subBal
      concreteCreateSender 1000000 = some concreteExitDebit := by
  have hb : (concreteDripped.state.incrNonce concreteCreateSender).bal concreteCreateSender =
      999999999998823644 := by
    unfold State.bal
    rw [State.incrNonce_get_bal]
    exact concreteDrippedSenderBalance
  change (concreteDripped.state.incrNonce concreteCreateSender).subBal concreteCreateSender
    1000000 = _
  unfold State.subBal
  rw [hb, if_neg (by decide +kernel)]
  unfold concreteExitDebit
  dsimp only
  rw [hb]

noncomputable def concreteExitTenv : Tenv :=
  deploymentTenv concreteExitTxInput concreteExitTx concreteCreateSender 0

noncomputable def concreteExitMessage : Msg := {
  benv := { concreteExitTxInput.beginTransaction with state := concreteExitDebit }
  tenv := concreteExitTenv
  caller := concreteCreateSender
  target := some concreteCreateTarget
  currentTarget := concreteCreateTarget
  gas := concreteExitTenv.stat.gas
  value := 0
  data := concreteExitTx.data
  code := concreteExitDebit.getCode concreteCreateTarget
  codeAddress := some concreteCreateTarget
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := concreteExitTenv.stat.accessListAddresses.insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])
  accessedStorageKeys := concreteExitTenv.stat.accessListStorageKeys
  disablePrecompiles := false }

theorem concreteExitMessage_prepared :
    prepareMessage { concreteExitTxInput.beginTransaction with state := concreteExitDebit }
      concreteExitTenv concreteExitTx = .ok concreteExitMessage := rfl

theorem concreteExitMessage_code : concreteExitMessage.code.toList = code := by
  change (concreteExitDebit.getCode concreteCreateTarget).toList = code
  unfold concreteExitDebit
  rw [State.setBal_getCode]
  change ((concreteDripped.state.incrNonce concreteCreateSender).get concreteCreateTarget).code.toList = code
  rw [State.incrNonce_get_code]
  change (concreteDripped.state.getCode concreteCreateTarget).toList = code
  rw [concreteDrippedCode, concreteJoinedCode, concreteDeploymentRoot.installed]
  simp [ByteArray.toList_eq_toList_data]

theorem concreteExitDebit_balance :
    concreteExitDebit.bal concreteCreateSender = 999999999997823644 := by
  unfold concreteExitDebit
  change ((concreteDripped.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteDripped.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, State.incrNonce_get_bal]
  change concreteDripped.state.bal concreteCreateSender - 1000000 = _
  rw [concreteDrippedSenderBalance]
  decide +kernel

noncomputable def concreteExitEntry : Benv :=
  concreteExitMessage.benv.withState
    ((concreteExitDebit.setBal concreteCreateSender
      (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0)

theorem concreteExitEntry_run :
    concreteExitMessage.benvAfterTransfer = .ok concreteExitEntry := by
  unfold concreteExitEntry concreteExitMessage
  generalize concreteExitDebit = debit
  generalize concreteExitTxInput.beginTransaction = begun
  generalize concreteExitTenv = tenv
  have hnot : ¬ debit.bal concreteCreateSender < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  simp only [Msg.benvAfterTransfer, if_true, Benv.subBal, State.subBal, hnot, if_false,
    bind, Option.bind, Option.toExcept, Except.bind, Benv.addBal, Benv.withState]

theorem concreteExitEntry_storage (address : Adr) :
    (concreteExitEntry.state.get address).stor = (concreteDripped.state.get address).stor := by
  change (((concreteExitDebit.setBal _ _).addBal _ _).get address).stor = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteExitDebit
  dsimp only
  rw [State.setBal_get_stor, State.incrNonce_get_stor]


noncomputable def concreteExitSevm : Sevm := initSevm (concreteExitMessage.withBenv concreteExitEntry)
noncomputable def concreteExitDevm : Devm := initDevm (concreteExitMessage.withBenv concreteExitEntry)

theorem concreteExitDevm_chi : concreteExitDevm.getStorVal concreteCreateTarget chiSlot = concreteDripChi := by
  change (concreteExitEntry.state.get concreteCreateTarget).stor.get chiSlot = concreteDripChi
  rw [concreteExitEntry_storage]
  exact concreteDripped_values.1

theorem concreteExitDevm_rho : concreteExitDevm.getStorVal concreteCreateTarget rhoSlot = 5 := by
  change (concreteExitEntry.state.get concreteCreateTarget).stor.get rhoSlot = 5
  rw [concreteExitEntry_storage]
  exact concreteDripped_values.2.1

theorem concreteExitDevm_cold (k : B256) :
    (concreteCreateTarget, k) ∉ concreteExitDevm.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∉ (∅ : Std.HashSet (Adr × B256))
  simp

theorem concreteJoinedTargetBalance : concreteJoined.state.bal concreteCreateTarget = 100 := by
  have hm : concreteJoinMessageState.bal concreteCreateTarget = concreteJoinEntry.state.bal concreteCreateTarget := by
    unfold concreteJoinMessageState concreteJoinRuntimePost
    rw [Devm.withOutput_state, Devm.setMach_state]
    have hs (d : Devm) (k v : B256) :
        (d.setStorVal concreteCreateTarget k v).getBal concreteCreateTarget =
          d.getBal concreteCreateTarget :=
      (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
    change (concreteJoinTotalBase).getBal concreteCreateTarget = _
    unfold concreteJoinTotalBase
    rw [hs]
    change (concreteJoinRowBase).getBal concreteCreateTarget = _
    unfold concreteJoinRowBase
    rw [hs]
    change (concreteJoinRhoBase).getBal concreteCreateTarget = _
    unfold concreteJoinRhoBase
    rw [hs]
    change (concreteJoinChiBase).getBal concreteCreateTarget = _
    unfold concreteJoinChiBase
    rw [hs]
    rfl
  have hz : (0 : Adr) ≠ concreteCreateTarget := by decide +kernel
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  change (concreteJoinTransactionState.get concreteCreateTarget).bal = _
  unfold concreteJoinTransactionState deploymentFinalState
  change (((concreteJoinMessageState.addBal concreteCreateSender 847712).addBal 0 76144).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_ne ht]
  change concreteJoinMessageState.bal concreteCreateTarget = _
  rw [hm]
  change (((concreteJoinDebit.setBal concreteCreateSender
    (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  simp only [State.bal, State.setBal_get_ne ht]
  change concreteJoinDebit.bal concreteCreateTarget + 100 = _
  unfold concreteJoinDebit State.bal
  rw [State.setBal_get_ne ht, State.incrNonce_get_bal]
  change concreteDeployed.state.bal concreteCreateTarget + 100 = _
  rw [concreteDeploymentRoot.bal]
  decide +kernel

theorem concreteDrippedTargetBalance : concreteDripped.state.bal concreteCreateTarget = 100 := by
  have hm : concreteDripMessageState.bal concreteCreateTarget = concreteDripEntry.state.bal concreteCreateTarget := by
    unfold concreteDripMessageState concreteDripRuntimePost
    rw [Devm.withOutput_state, Devm.setMach_state]
    have hs (d : Devm) (k v : B256) :
        (d.setStorVal concreteCreateTarget k v).getBal concreteCreateTarget =
          d.getBal concreteCreateTarget :=
      (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
    change (concreteDripRhoBase).getBal concreteCreateTarget = _
    unfold concreteDripRhoBase
    rw [hs]
    change (concreteDripChiBase).getBal concreteCreateTarget = _
    unfold concreteDripChiBase
    rw [hs]
    rfl
  have hz : (0 : Adr) ≠ concreteCreateTarget := by decide +kernel
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  change (concreteDripTransactionState.get concreteCreateTarget).bal = _
  unfold concreteDripTransactionState deploymentFinalState
  change (((concreteDripMessageState.addBal concreteCreateSender 935850).addBal 0 32075).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_ne ht]
  change concreteDripMessageState.bal concreteCreateTarget = _
  rw [hm]
  change (((concreteDripDebit.setBal concreteCreateSender
    (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  simp only [State.bal, State.setBal_get_ne ht]
  change concreteDripDebit.bal concreteCreateTarget + 0 = _
  unfold concreteDripDebit State.bal
  rw [State.setBal_get_ne ht, State.incrNonce_get_bal]
  change concreteJoined.state.bal concreteCreateTarget + 0 = _
  rw [concreteJoinedTargetBalance]
  decide +kernel

theorem concreteExitDevm_balance : concreteExitDevm.getBal concreteCreateTarget = 100 := by
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  change (((concreteExitDebit.setBal concreteCreateSender
    (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  simp only [State.bal, State.setBal_get_ne ht]
  change concreteExitDebit.bal concreteCreateTarget + 0 = _
  unfold concreteExitDebit State.bal
  rw [State.setBal_get_ne ht, State.incrNonce_get_bal]
  change concreteDripped.state.bal concreteCreateTarget + 0 = _
  rw [concreteDrippedTargetBalance]
  decide +kernel

def concreteExitArgumentMemory : Mem :=
  ((Mem.empty.write 64 (40 : B256).toBytes).write 96 (99 : B256).toBytes).write 128 (99 : B256).toBytes

def concreteExitStagingMemory : Mem := concreteExitArgumentMemory.write 32 (2 : B256).toBytes

private theorem concreteExit_stateGas_none : concreteExitSevm.benvStat.rules.stateGas = none := by
  exact CoveredFork.prague.rules_stateGas_none

private theorem concreteExit_stage (base post : Devm) (G : Nat)
    (hrow : base.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 99)
    (htotal : base.getStorVal concreteCreateTarget totalUnitsSlot = 99)
    (hcoldRow : (concreteCreateTarget, concreteCreateSender.toB256) ∉ base.accessedStorageKeys)
    (hcoldTotal : (concreteCreateTarget, totalUnitsSlot) ∉ base.accessedStorageKeys)
    (hfresh : Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      ((concreteJoinStagingBase base).setMach ⟨[], concreteExitStagingMemory, G, (concreteJoinStagingBase base).stateGas⟩)
      freshStart post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (base.setMach ⟨[], Mem.empty, G + 4387, base.stateGas⟩) exit post := by
  have harg : Sevm.dataWord concreteExitSevm (32 * 0 + 4) = 40 := by
    change Bytes.toB256 (concreteExitTx.data.sliceD 4 32 0) = 40
    decide +kernel
  func_run (2)
  rw [harg]
  func_run (7) [9, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  func_run (1)
  · exact concreteExit_stateGas_none
  change Func.RunCompiled _ concreteExitSevm
    ((addAccessedStorageKey _ concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[base.getStorVal concreteCreateTarget concreteCreateSender.toB256],
        Mem.empty.write 64 (40 : B256).toBytes, G + 4387 - 2145, base.stateGas⟩) _ post
  rw [hrow]
  func_run (7) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteExitSevm
    ((addAccessedStorageKey base concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[totalUnitsSlot], (Mem.empty.write 64 (40 : B256).toBytes).write 96 (99 : B256).toBytes,
        G + 4387 - 2179, base.stateGas⟩) _ post
  func_run (1)
  · exact concreteExit_stateGas_none
  · change (concreteCreateTarget, totalUnitsSlot) ∉
      base.accessedStorageKeys.insert (concreteCreateTarget, concreteCreateSender.toB256)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by decide +kernel, hcoldTotal⟩
  change Func.RunCompiled _ concreteExitSevm
    ((concreteJoinStagingBase base).setMach
      ⟨[base.getStorVal concreteCreateTarget totalUnitsSlot],
        (Mem.empty.write 64 (40 : B256).toBytes).write 96 (99 : B256).toBytes,
        G + 4387 - 4279, (concreteJoinStagingBase base).stateGas⟩) _ post
  rw [htotal]
  func_run (6) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteExitSevm
    ((concreteJoinStagingBase base).setMach ⟨[], concreteExitArgumentMemory, G + 4387 - 4310, (concreteJoinStagingBase base).stateGas⟩) _ post
  have hs : concreteExitArgumentMemory.size = 160 := by decide +kernel
  have ha : Bytes.toB256 (concreteExitArgumentMemory.read 64 32).1 = 40 := by decide +kernel
  have hr : Bytes.toB256 (concreteExitArgumentMemory.read 96 32).1 = 99 := by decide +kernel
  have ht : Bytes.toB256 (concreteExitArgumentMemory.read 128 32).1 = 99 := by decide +kernel
  have hm (n : Nat) (hn : n + 32 ≤ 160) :
      (concreteExitArgumentMemory.read n 32).2 = concreteExitArgumentMemory :=
    Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by decide) hn)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (argumentWord * 32).toNat = 64 by decide +kernel, ha, hm 64 (by decide)]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (rowWord * 32).toNat = 96 by decide +kernel, hr, hm 96 (by decide)]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (argumentWord * 32).toNat = 64 by decide +kernel, ha, hm 64 (by decide)]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (totalWord * 32).toNat = 128 by decide +kernel, ht, hm 128 (by decide)]
  func_run (2) [0]
  func_run (3) [0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteExitSevm
    ((concreteJoinStagingBase base).setMach ⟨[], concreteExitStagingMemory, G + 4387 - 4375, (concreteJoinStagingBase base).stateGas⟩)
    (.call freshStartSlot) post
  apply Func.runCompiled_call' (f := freshStart) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hfresh

private theorem concreteExit_readChi (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat) (next : Func)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = concreteDripChi)
    (hcold : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach ⟨[concreteDripChi], M, G, base.stateGas⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2103, base.stateGas⟩)
      (Ninst.pushB256 chiSlot ::: Ninst.sload ::: next) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget chiSlot], M, G + 2103 - 2103, base.stateGas⟩) next post
  simpa only [hchi, Nat.add_sub_cancel] using htail


private theorem concreteExit_stageClock (sevm : Sevm) (base post : Devm) (M C : Mem)
    (G : Nat) (next : Func) (htime : sevm.benvStat.time = 6)
    (hsize : M.size = 160)
    (hstore : M.write (storedChiWord * 32).toNat concreteDripChi.toBytes = C)
    (hcsize : C.size = 192)
    (hread : Bytes.toB256 (C.read (storedChiWord * 32).toNat 32).1 = concreteDripChi)
    (hmem : (C.read (storedChiWord * 32).toNat 32).2 = C)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], C.write 192 (6 : B256).toBytes, G, base.stateGas⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G + 70, base.stateGas⟩)
      (mstoreAt storedChiWord +++
        (Ninst.pushB256 scale ::: loadWord storedChiWord +++ Ninst.lt :::
          (.revert <?>
            (loadWord storedChiWord +++ Ninst.pushB256 maxChi ::: Ninst.lt :::
              (.revert <?> (Ninst.timestamp ::: mstoreAt nowWord +++ next)))))) post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (3) [0]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [htime]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], C.write 192 (6 : B256).toBytes, G + 70 - 70, base.stateGas⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteExit_stageElapsed (sevm : Sevm) (base post : Devm) (M E : Mem)
    (G : Nat) (next : Func)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 5)
    (hcold : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hsize : M.size = 224)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 6)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hstore : M.write (exponentWord * 32).toNat (1 : B256).toBytes = E)
    (hesize : E.size = 224)
    (hexp : Bytes.toB256 (E.read (exponentWord * 32).toNat 32).1 = 1)
    (hemem : (E.read (exponentWord * 32).toNat 32).2 = E)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach ⟨[], E, G, base.stateGas⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2166, base.stateGas⟩)
      (Ninst.pushB256 rhoSlot ::: Ninst.sload ::: Ninst.dup 0 :::
        loadWord nowWord +++ Ninst.lt :::
          (.revert <?> (loadWord nowWord +++ Ninst.sub :::
            mstoreAt exponentWord +++ loadWord exponentWord +++
            Ninst.pushB256 maxElapsed ::: Ninst.lt ::: (.revert <?> next)))) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget rhoSlot], M, G + 2166 - 2103, base.stateGas⟩) _ post
  rw [hrho]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (3) [1, 0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hesize]
    decide +kernel
  rw [hexp, hemem]
  func_run (3) [0]
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteExit_initializeRpow (sevm : Sevm) (base post : Devm) (M B A Z : Mem)
    (G : Nat) (zeroBase zeroExponent evenExponent : Func)
    (hsize : M.size = 224)
    (hbase : M.write (baseWord * 32).toNat rate.toBytes = B)
    (hbsize : B.size = 256)
    (hbexp : Bytes.toB256 (B.read (exponentWord * 32).toNat 32).1 = 1)
    (hbmem : (B.read (exponentWord * 32).toNat 32).2 = B)
    (hacc : B.write (accumulatorWord * 32).toNat rate.toBytes = A)
    (hasize : A.size = 288)
    (haexp : Bytes.toB256 (A.read (exponentWord * 32).toNat 32).1 = 1)
    (hamem : (A.read (exponentWord * 32).toNat 32).2 = A)
    (hzero : A.write (exponentWord * 32).toNat (0 : B256).toBytes = Z)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Z, G, base.stateGas⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 122, base.stateGas⟩)
      (Ninst.pushB256 rate ::: Ninst.dup 0 ::: mstoreAt baseWord +++ Ninst.iszero :::
        (zeroBase <?> (loadWord exponentWord +++ Ninst.iszero :::
          (zeroExponent <?> (loadWord exponentWord +++ Ninst.pushB256 1 ::: Ninst.and :::
            ((Ninst.pushB256 rate ::: mstoreAt accumulatorWord +++ loadWord exponentWord +++
              Ninst.pushB256 2 ::: Ninst.swap 0 ::: Ninst.div ::: mstoreAt exponentWord +++
              .call rpowLoopSlot) <?> evenExponent)))))) post := by
  func_run (4) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (3) [1]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hacc]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [haexp, hamem]
  func_run (5) [0, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [hzero]
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hloop


def concreteExitClockMemory : Mem :=
  (concreteExitStagingMemory.write 160 concreteDripChi.toBytes).write 192 (6 : B256).toBytes
def concreteExitExponentMemory : Mem := concreteExitClockMemory.write 0 (1 : B256).toBytes
def concreteExitBaseMemory : Mem := concreteExitExponentMemory.write 224 rate.toBytes
def concreteExitAccumulatorMemory : Mem := concreteExitBaseMemory.write 256 rate.toBytes
def concreteExitLoopMemory : Mem := concreteExitAccumulatorMemory.write 0 (0 : B256).toBytes

private theorem concreteExit_stagingSize : concreteExitStagingMemory.size = 160 := by decide +kernel

private theorem concreteExit_chiMemoryFacts :
    (concreteExitStagingMemory.write 160 concreteDripChi.toBytes).size = 192 ∧
    Bytes.toB256 ((concreteExitStagingMemory.write 160 concreteDripChi.toBytes).read 160 32).1 = concreteDripChi ∧
    ((concreteExitStagingMemory.write 160 concreteDripChi.toBytes).read 160 32).2 =
      concreteExitStagingMemory.write 160 concreteDripChi.toBytes := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_clockMemoryFacts : concreteExitClockMemory.size = 224 ∧
    Bytes.toB256 (concreteExitClockMemory.read 192 32).1 = 6 ∧
    (concreteExitClockMemory.read 192 32).2 = concreteExitClockMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_exponentMemoryFacts : concreteExitExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteExitExponentMemory.read 0 32).1 = 1 ∧
    (concreteExitExponentMemory.read 0 32).2 = concreteExitExponentMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_baseMemoryFacts : concreteExitBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteExitBaseMemory.read 0 32).1 = 1 ∧
    (concreteExitBaseMemory.read 0 32).2 = concreteExitBaseMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_accumulatorMemoryFacts : concreteExitAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteExitAccumulatorMemory.read 0 32).1 = 1 ∧
    (concreteExitAccumulatorMemory.read 0 32).2 = concreteExitAccumulatorMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

theorem concreteExit_freshStart (sevm : Sevm) (base post : Devm) (G : Nat)
    (htime : sevm.benvStat.time = 6)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = concreteDripChi)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 5)
    (hcoldChi : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (hcoldRho : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((concreteDripFreshBase sevm base).setMach ⟨[], concreteExitLoopMemory, G, (concreteDripFreshBase sevm base).stateGas⟩)
      rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteExitStagingMemory, G + 122 + 2166 + 70 + 2103, base.stateGas⟩)
      freshStart post := by
  apply concreteExit_readChi sevm _ _ _ _ _ hsg hchi hcoldChi
  apply concreteExit_stageClock (sevm := sevm) (C := concreteExitStagingMemory.write 160 concreteDripChi.toBytes)
  · exact htime
  · exact concreteExit_stagingSize
  · rfl
  · exact concreteExit_chiMemoryFacts.1
  · exact concreteExit_chiMemoryFacts.2.1
  · exact concreteExit_chiMemoryFacts.2.2
  apply concreteExit_stageElapsed (E := concreteExitExponentMemory) (hsg := hsg)
  · exact hrho
  · change (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys.insert
      (sevm.currentTarget, chiSlot)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by simp only [beq_iff_eq, Prod.mk.injEq, true_and]; decide +kernel, hcoldRho⟩
  · exact concreteExit_clockMemoryFacts.1
  · exact concreteExit_clockMemoryFacts.2.1
  · exact concreteExit_clockMemoryFacts.2.2
  · rfl
  · exact concreteExit_exponentMemoryFacts.1
  · exact concreteExit_exponentMemoryFacts.2.1
  · exact concreteExit_exponentMemoryFacts.2.2
  apply concreteExit_initializeRpow (B := concreteExitBaseMemory)
    (A := concreteExitAccumulatorMemory) (Z := concreteExitLoopMemory)
  · exact concreteExit_exponentMemoryFacts.1
  · rfl
  · exact concreteExit_baseMemoryFacts.1
  · exact concreteExit_baseMemoryFacts.2.1
  · exact concreteExit_baseMemoryFacts.2.2
  · rfl
  · exact concreteExit_accumulatorMemoryFacts.1
  · exact concreteExit_accumulatorMemoryFacts.2.1
  · exact concreteExit_accumulatorMemoryFacts.2.2
  · rfl
  exact hloop


def concreteExitChi : B256 := 1000000007735629813252049571

private def concreteExitLoopImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 64 (40 : B256).toBytes) 96 (99 : B256).toBytes) 128 (99 : B256).toBytes) 32 (2 : B256).toBytes) 160 concreteDripChi.toBytes) 192 (6 : B256).toBytes) 0 (1 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (0 : B256).toBytes)

private theorem concreteExit_loopReads : Mem.Reads concreteExitLoopMemory concreteExitLoopImage := by
  unfold concreteExitLoopMemory concreteExitAccumulatorMemory concreteExitBaseMemory concreteExitExponentMemory concreteExitClockMemory concreteExitStagingMemory concreteExitArgumentMemory concreteExitLoopImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteExit_loopSize : concreteExitLoopMemory.size = 288 := by
  unfold concreteExitLoopMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteExit_accumulatorMemoryFacts.1]; decide)]
  exact concreteExit_accumulatorMemoryFacts.1

private theorem concreteExit_loopUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteExitLoopMemory.read i 32).2 = concreteExitLoopMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteExit_loopSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteExit_loopRead0 :
    Bytes.toB256 (concreteExitLoopMemory.read 0 32).1 = (0 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead32 :
    Bytes.toB256 (concreteExitLoopMemory.read 32 32).1 = (2 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead64 :
    Bytes.toB256 (concreteExitLoopMemory.read 64 32).1 = (40 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 128 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 96 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead96 :
    Bytes.toB256 (concreteExitLoopMemory.read 96 32).1 = (99 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 128 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead128 :
    Bytes.toB256 (concreteExitLoopMemory.read 128 32).1 = (99 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 32 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead160 :
    Bytes.toB256 (concreteExitLoopMemory.read 160 32).1 = concreteDripChi := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 192 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead192 :
    Bytes.toB256 (concreteExitLoopMemory.read 192 32).1 = (6 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead256 :
    Bytes.toB256 (concreteExitLoopMemory.read 256 32).1 = rate := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_composeFresh (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hchi : Bytes.toB256 (M.read (storedChiWord * 32).toNat 32).1 = concreteDripChi)
    (hchiMem : (M.read (storedChiWord * 32).toNat 32).2 = M)
    (hfactor : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = rate)
    (hfactorMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hroute : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G, base.stateGas⟩) freshRoute post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 104, base.stateGas⟩) composeFresh post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [concreteDripChi * rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [concreteDripChi, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (3) [1, 0]
  func_run (7) [concreteExitChi, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  apply Func.runCompiled_call' (f := freshRoute) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hroute

private theorem concreteExit_freshRoute (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hroute : Bytes.toB256 (M.read (routeWord * 32).toNat 32).1 = routeExit)
    (hmem : (M.read (routeWord * 32).toNat 32).2 = M)
    (hexit : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G, base.stateGas⟩) afterExit post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G + 53, base.stateGas⟩) freshRoute post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hroute, hmem]
  func_run (9) [0, 1]
  simpa only [Nat.add_sub_cancel] using hexit


private theorem concreteExit_beforeCall (sevm : Sevm) (base C R U T post : Devm) (M : Mem) (G : Nat)
    (hstatic : sevm.isStatic = false) (hfork : CoveredFork sevm.benvStat.fork)
    (hsize : M.size = 288)
    (harg : Bytes.toB256 (M.read (argumentWord * 32).toNat 32).1 = 40)
    (hargMem : (M.read (argumentWord * 32).toNat 32).2 = M)
    (hrow : Bytes.toB256 (M.read (rowWord * 32).toNat 32).1 = 99)
    (hrowMem : (M.read (rowWord * 32).toNat 32).2 = M)
    (htotal : Bytes.toB256 (M.read (totalWord * 32).toNat 32).1 = 99)
    (htotalMem : (M.read (totalWord * 32).toNat 32).2 = M)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 6)
    (hnowMem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hchiCost : sstoreCost sevm base chiSlot concreteExitChi = 2900)
    (hchi : afterSstore sevm base chiSlot concreteExitChi = C)
    (hrhoCost : sstoreCost sevm C rhoSlot 6 = 2900)
    (hrho : afterSstore sevm C rhoSlot 6 = R)
    (hrowCost : sstoreCost sevm R sevm.caller.toB256 59 = 2900)
    (hrowStore : afterSstore sevm R sevm.caller.toB256 59 = U)
    (htotalCost : sstoreCost sevm U totalUnitsSlot 59 = 2900)
    (htotalStore : afterSstore sevm U totalUnitsSlot 59 = T)
    (hcall : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (T.setMach ⟨[40], M, G, T.stateGas⟩)
      (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G + 11675, base.stateGas⟩) afterExit post := by
  have hkeep : ∀ (D : Devm) (key value : B256),
      (afterSstore sevm D key value).stateGas = D.stateGas :=
    fun _ _ _ => afterSstore_stateGas
  have hCStateGas : C.stateGas = base.stateGas := hchi ▸ hkeep base chiSlot concreteExitChi
  have hRStateGas : R.stateGas = C.stateGas := hrho ▸ hkeep C rhoSlot 6
  have hUStateGas : U.stateGas = R.stateGas := hrowStore ▸ hkeep R sevm.caller.toB256 59
  have hTStateGas : T.stateGas = U.stateGas := htotalStore ▸ hkeep U totalUnitsSlot 59
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (5) [concreteExitChi * 40, 40]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  func_run (2)
  rw [show G + 11675 - 31 = (G + 8744) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := C.setMach ⟨[40], M, G + 8744, base.stateGas⟩) ?_ ?_
  · simpa only [hchiCost, hchi] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := base)
        (key := chiSlot) (value := concreteExitChi) (stack := [40]) (memory := M) (G := G + 8744) hfork
        (by rw [hchiCost]; simp only [gCallStipend]; omega) hstatic)
  rw [← hCStateGas]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hnowMem]
  func_run (1)
  rw [show G + 8744 - 9 = (G + 5835) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := R.setMach ⟨[40], M, G + 5835, C.stateGas⟩) ?_ ?_
  · simpa only [hrhoCost, hrho] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := C)
        (key := rhoSlot) (value := 6) (stack := [40]) (memory := M) (G := G + 5835) hfork
        (by rw [hrhoCost]; simp only [gCallStipend]; omega) hstatic)
  rw [← hRStateGas]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hrow, hrowMem]
  func_run (2) [59]
  rw [show G + 5835 - 17 = (G + 2918) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := U.setMach ⟨[40], M, G + 2918, R.stateGas⟩) ?_ ?_
  · simpa only [hrowCost, hrowStore] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := R)
        (key := sevm.caller.toB256) (value := 59) (stack := [40]) (memory := M) (G := G + 2918) hfork
        (by rw [hrowCost]; simp only [gCallStipend]; omega) hstatic)
  rw [← hUStateGas]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [htotal, htotalMem]
  func_run (2) [59]
  rw [show G + 2918 - 18 = G + 2900 by omega]
  refine Func.RunCompiled.next (devm' := T.setMach ⟨[40], M, G, U.stateGas⟩) ?_ ?_
  · simpa only [htotalCost, htotalStore] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := U)
        (key := totalUnitsSlot) (value := 59) (stack := [40]) (memory := M) (G := G) hfork
        (by rw [htotalCost]; simp only [gCallStipend]; omega) hstatic)
  rw [← hTStateGas]
  exact hcall

theorem concreteExitDevm_units :
    concreteExitDevm.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 99 ∧
    concreteExitDevm.getStorVal concreteCreateTarget totalUnitsSlot = 99 := by
  change (concreteExitEntry.state.get concreteCreateTarget).stor.get concreteCreateSender.toB256 = 99 ∧
    (concreteExitEntry.state.get concreteCreateTarget).stor.get totalUnitsSlot = 99
  rw [concreteExitEntry_storage]
  exact concreteDripped_values.2.2

noncomputable def concreteExitStorageBase : Devm :=
  concreteDripFreshBase concreteExitSevm (concreteJoinStagingBase concreteExitDevm)
noncomputable def concreteExitChiBase : Devm :=
  (concreteExitStorageBase.withRefundCounter 0).setStorVal concreteCreateTarget chiSlot concreteExitChi
noncomputable def concreteExitRhoBase : Devm :=
  (concreteExitChiBase.withRefundCounter 0).setStorVal concreteCreateTarget rhoSlot 6
noncomputable def concreteExitRowBase : Devm :=
  (concreteExitRhoBase.withRefundCounter 0).setStorVal concreteCreateTarget concreteCreateSender.toB256 59
noncomputable def concreteExitTotalBase : Devm :=
  (concreteExitRowBase.withRefundCounter 0).setStorVal concreteCreateTarget totalUnitsSlot 59

private theorem concreteExit_originalStorage (key : B256) :
    getOrigStorVal concreteExitSevm concreteCreateTarget key =
      (concreteDripped.state.getStor concreteCreateTarget).get key := by rfl

private theorem concreteExitStorageBase_warm (key : B256)
    (hk : key = chiSlot ∨ key = rhoSlot ∨ key = concreteCreateSender.toB256 ∨ key = totalUnitsSlot) :
    (concreteCreateTarget, key) ∈ concreteExitStorageBase.accessedStorageKeys := by
  change (concreteCreateTarget, key) ∈ (((concreteExitDevm.accessedStorageKeys.insert
    (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)).insert
      (concreteCreateTarget, chiSlot)).insert (concreteCreateTarget, rhoSlot)
  rcases hk with rfl | rfl | rfl | rfl <;> simp

private theorem concreteExit_chiStore :
    sstoreCost concreteExitSevm concreteExitStorageBase chiSlot concreteExitChi = 2900 ∧
    afterSstore concreteExitSevm concreteExitStorageBase chiSlot concreteExitChi = concreteExitChiBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, chiSlot) ∈ concreteExitStorageBase.accessedStorageKeys := by
    exact concreteExitStorageBase_warm chiSlot (Or.inl rfl)
  have hr : concreteExitStorageBase.refundCounter = 0 := rfl
  have hv : concreteExitStorageBase.getStorVal concreteCreateTarget chiSlot = concreteDripChi := by
    change (Devm.getStor concreteExitStorageBase concreteCreateTarget).get chiSlot = _
    exact concreteExitDevm_chi
  have hc : sstoreValueCost concreteDripChi concreteDripChi concreteExitChi = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteExitSevm.benvStat.rules.gas concreteExitChi concreteDripChi concreteDripChi 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.1, hv, hr, hf]
    rfl

private theorem concreteExit_rhoStore :
    sstoreCost concreteExitSevm concreteExitChiBase rhoSlot 6 = 2900 ∧
    afterSstore concreteExitSevm concreteExitChiBase rhoSlot 6 = concreteExitRhoBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, rhoSlot) ∈ concreteExitChiBase.accessedStorageKeys := by
    rw [concreteExitChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteExitStorageBase_warm rhoSlot (Or.inr (Or.inl rfl))
  have hr : concreteExitChiBase.refundCounter = 0 := rfl
  have hv : concreteExitChiBase.getStorVal concreteCreateTarget rhoSlot = 5 := by
    change (Devm.getStor concreteExitChiBase concreteCreateTarget).get rhoSlot = _
    unfold concreteExitChiBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteExitDevm_rho
  have hc : sstoreValueCost 5 5 6 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteExitSevm.benvStat.rules.gas 6 5 5 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.2.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.2.1, hv, hr, hf]
    rfl

private theorem concreteExit_rowStore :
    sstoreCost concreteExitSevm concreteExitRhoBase concreteCreateSender.toB256 59 = 2900 ∧
    afterSstore concreteExitSevm concreteExitRhoBase concreteCreateSender.toB256 59 = concreteExitRowBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, concreteCreateSender.toB256) ∈ concreteExitRhoBase.accessedStorageKeys := by
    rw [concreteExitRhoBase, Devm.sstoreWarmBase_accessedStorageKeys]
    rw [concreteExitChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteExitStorageBase_warm concreteCreateSender.toB256 (Or.inr (Or.inr (Or.inl rfl)))
  have hr : concreteExitRhoBase.refundCounter = 0 := rfl
  have hv : concreteExitRhoBase.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 99 := by
    change (Devm.getStor concreteExitRhoBase concreteCreateTarget).get concreteCreateSender.toB256 = _
    unfold concreteExitRhoBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    unfold concreteExitChiBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteExitDevm_units.1
  have hc : sstoreValueCost 99 99 59 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteExitSevm.benvStat.rules.gas 59 99 99 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.2.2.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.2.2.1, hv, hr, hf]
    rfl

private theorem concreteExit_totalStore :
    sstoreCost concreteExitSevm concreteExitRowBase totalUnitsSlot 59 = 2900 ∧
    afterSstore concreteExitSevm concreteExitRowBase totalUnitsSlot 59 = concreteExitTotalBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, totalUnitsSlot) ∈ concreteExitRowBase.accessedStorageKeys := by
    rw [concreteExitRowBase, Devm.sstoreWarmBase_accessedStorageKeys]
    rw [concreteExitRhoBase, Devm.sstoreWarmBase_accessedStorageKeys]
    rw [concreteExitChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteExitStorageBase_warm totalUnitsSlot (Or.inr (Or.inr (Or.inr rfl)))
  have hr : concreteExitRowBase.refundCounter = 0 := rfl
  have hv : concreteExitRowBase.getStorVal concreteCreateTarget totalUnitsSlot = 99 := by
    change (Devm.getStor concreteExitRowBase concreteCreateTarget).get totalUnitsSlot = _
    unfold concreteExitRowBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    unfold concreteExitRhoBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    unfold concreteExitChiBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteExitDevm_units.2
  have hc : sstoreValueCost 99 99 59 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteExitSevm.benvStat.rules.gas 59 99 99 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.2.2.2, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.2.2.2, hv, hr, hf]
    rfl

private theorem concreteExit_prefix (G : Nat) (post : Devm)
    (hcall : Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitTotalBase.setMach ⟨[40], concreteExitLoopMemory, G, concreteExitTotalBase.stateGas⟩)
      (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitDevm.setMach ⟨[], Mem.empty, G + 20714, concreteExitDevm.stateGas⟩) exit post := by
  change Func.RunCompiled _ _
    (concreteExitDevm.setMach ⟨[], Mem.empty, G + 11675 + 53 + 104 + 34 + 122 + 2166 + 70 + 2103 + 4387, concreteExitDevm.stateGas⟩) _ _
  apply concreteExit_stage
  · exact concreteExitDevm_units.1
  · exact concreteExitDevm_units.2
  · exact concreteExitDevm_cold _
  · exact concreteExitDevm_cold _
  apply concreteExit_freshStart
  · rfl
  · exact concreteExit_stateGas_none
  · exact concreteExitDevm_chi
  · exact concreteExitDevm_rho
  · change (concreteCreateTarget, chiSlot) ∉
      (concreteExitDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteExitDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  · change (concreteCreateTarget, rhoSlot) ∉
      (concreteExitDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteExitDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  apply concreteDrip_rpowZero
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead0
  · exact concreteExit_loopUnchanged 0 (by decide)
  apply concreteExit_composeFresh
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead160
  · exact concreteExit_loopUnchanged 160 (by decide)
  · exact concreteExit_loopRead256
  · exact concreteExit_loopUnchanged 256 (by decide)
  apply concreteExit_freshRoute
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead32
  · exact concreteExit_loopUnchanged 32 (by decide)
  apply concreteExit_beforeCall _ concreteExitStorageBase concreteExitChiBase concreteExitRhoBase
    concreteExitRowBase concreteExitTotalBase
  · rfl
  · exact CoveredFork.prague
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead64
  · exact concreteExit_loopUnchanged 64 (by decide)
  · exact concreteExit_loopRead96
  · exact concreteExit_loopUnchanged 96 (by decide)
  · exact concreteExit_loopRead128
  · exact concreteExit_loopUnchanged 128 (by decide)
  · exact concreteExit_loopRead192
  · exact concreteExit_loopUnchanged 192 (by decide)
  · exact concreteExit_chiStore.1
  · exact concreteExit_chiStore.2
  · exact concreteExit_rhoStore.1
  · exact concreteExit_rhoStore.2
  · exact concreteExit_rowStore.1
  · exact concreteExit_rowStore.2
  · exact concreteExit_totalStore.1
  · exact concreteExit_totalStore.2
  exact hcall

theorem concreteExitTotalBase_balance : concreteExitTotalBase.getBal concreteCreateTarget = 100 := by
  have hs (d : Devm) (k v : B256) :
      (d.setStorVal concreteCreateTarget k v).getBal concreteCreateTarget = d.getBal concreteCreateTarget :=
    (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
  unfold concreteExitTotalBase
  rw [hs]
  change concreteExitRowBase.getBal concreteCreateTarget = _
  unfold concreteExitRowBase
  rw [hs]
  change concreteExitRhoBase.getBal concreteCreateTarget = _
  unfold concreteExitRhoBase
  rw [hs]
  change concreteExitChiBase.getBal concreteCreateTarget = _
  unfold concreteExitChiBase
  rw [hs]
  exact concreteExitDevm_balance

theorem concreteExitTotalBase_storage : Devm.getStor concreteExitTotalBase concreteCreateTarget =
    ((((concreteDripped.state.getStor concreteCreateTarget).set chiSlot concreteExitChi).set rhoSlot 6).set
      concreteCreateSender.toB256 59).set totalUnitsSlot 59 := by
  unfold concreteExitTotalBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteExitRowBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteExitRhoBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteExitChiBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  have hs : Devm.getStor concreteExitStorageBase concreteCreateTarget =
      concreteDripped.state.getStor concreteCreateTarget := concreteExitEntry_storage _
  rw [hs]

theorem concreteExitTotalBase_code (a : Adr) :
    concreteExitTotalBase.getCode a = concreteDripped.state.getCode a := by
  unfold concreteExitTotalBase
  rw [Devm.setStorVal_getCode]
  change concreteExitRowBase.getCode a = _
  unfold concreteExitRowBase
  rw [Devm.setStorVal_getCode]
  change concreteExitRhoBase.getCode a = _
  unfold concreteExitRhoBase
  rw [Devm.setStorVal_getCode]
  change concreteExitChiBase.getCode a = _
  unfold concreteExitChiBase
  rw [Devm.setStorVal_getCode]
  change concreteExitEntry.state.getCode a = _
  change ((concreteExitDebit.setBal _ _).addBal _ _).getCode a = _
  rw [State.addBal_getCode, State.setBal_getCode]
  unfold concreteExitDebit
  rw [State.setBal_getCode]
  change ((concreteDripped.state.incrNonce concreteCreateSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl

private theorem concreteExit_dispatch (sevm : Sevm) (base post : Devm) (G : Nat)
    (hdata : sevm.data = concreteExitTx.data)
    (hvalue : sevm.value = 0)
    (hexit : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩) exit post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
    (base.setMach ⟨[], Mem.empty, G + 156, base.stateGas⟩) main post := by
  have hd : dripSelector = (0x9f678cca : B256) := by decide +kernel
  have hj : joinSelector = (0xb688a363 : B256) := by decide +kernel
  have hx : exitSelector = (0x7f8661a1 : B256) := by decide +kernel
  have hu : convertToUnitsSelector = (0x9227149a : B256) := by decide +kernel
  have hshift : Sevm.dataWord sevm 0 >>> B256.toNat 224 = exitSelector := by
    simp only [Sevm.dataWord, hdata, concreteExitTx]
    decide +kernel
  func_run (1)
  simp only [hdata, concreteExitTx]
  func_run (5) [exitSelector]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[exitSelector], Mem.empty, G + 156 - 27, base.stateGas⟩) (dispatch tree) post
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[exitSelector], Mem.empty, G + 156 - 27, base.stateGas⟩)
    (Ninst.dup 0 ::: Ninst.pushB256 dripSelector ::: Ninst.gt :::
      (dispatch (.fork (.fork (.leaf convertToAssetsSelector (nonpayable (exactCalldata 36 convertToAssets)))
          (.leaf exitSelector (nonpayable (exactCalldata 36 exit))))
        (.leaf convertToUnitsSelector (nonpayable (exactCalldata 36 convertToUnits)))) <?>
       dispatch (.fork (.leaf dripSelector (nonpayable (exactCalldata 4 drip)))
         (.leaf joinSelector (exactCalldata 4 join))))) post
  simp only [hd, hj, hx, hu]
  func_run (4) [1]
  func_run (4) [1]
  func_run (4) [0]
  func_run (3) [1]
  func_run (1)
  rw [hvalue]
  func_run (2) [1]
  func_run (4) [1]
  all_goals first
    | simpa only [Nat.add_sub_cancel] using hexit
    | (simp only [hdata, concreteExitTx]; decide +kernel)

noncomputable def concreteExitCallInput : Devm :=
  concreteExitTotalBase.setMach
    ⟨[457907, concreteCreateSender.toB256, 40, 0, 0, 0, 0, 40],
      concreteExitLoopMemory, 457907, concreteExitTotalBase.stateGas⟩

noncomputable def concreteExitCallResolved : Devm :=
  addAccessedAddress
    (concreteExitTotalBase.setMach ⟨[40], concreteExitLoopMemory, 457907, concreteExitTotalBase.stateGas⟩)
    concreteCreateSender

private theorem concreteExitTotalBase_senderBalance :
    concreteExitTotalBase.getBal concreteCreateSender = 999999999997823644 := by
  have hs (d : Devm) (k v : B256) :
      (d.setStorVal concreteCreateTarget k v).getBal concreteCreateSender = d.getBal concreteCreateSender :=
    (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
  unfold concreteExitTotalBase
  rw [hs]
  change concreteExitRowBase.getBal concreteCreateSender = _
  unfold concreteExitRowBase
  rw [hs]
  change concreteExitRhoBase.getBal concreteCreateSender = _
  unfold concreteExitRhoBase
  rw [hs]
  change concreteExitChiBase.getBal concreteCreateSender = _
  unfold concreteExitChiBase
  rw [hs]
  change (((concreteExitDebit.setBal concreteCreateSender
    (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
      concreteCreateSender).bal = _
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self, Acct.withBal]
  rw [concreteExitDebit_balance]
  decide +kernel

private theorem concreteExitCallResolved_code :
    concreteExitCallResolved.getCode concreteCreateSender = ByteArray.empty := by
  unfold concreteExitCallResolved
  rw [addAccessedAddress_getCode]
  change concreteExitTotalBase.getCode concreteCreateSender = _
  rw [concreteExitTotalBase_code, concreteDrippedSenderCode]

private theorem concreteExitCallResolved_senderBalance :
    concreteExitCallResolved.getBal concreteCreateSender = 999999999997823644 :=
  concreteExitTotalBase_senderBalance

private theorem concreteExitCallResolved_targetBalance :
    concreteExitCallResolved.getBal concreteCreateTarget = 100 :=
  concreteExitTotalBase_balance

private theorem concreteExitCall_warm :
    accessCost concreteCreateSender concreteExitTotalBase.accessedAddresses = 100 := by
  change accessCost concreteCreateSender ((Std.HashSet.ofList [0]).insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])) = 100
  simp [accessCost, Std.HashSet.mem_insertMany_list, gasWarmAccess]

/-- Actual value-bearing empty-code child execution, with the exact parent gas split. -/
private theorem concreteExit_call_exists :
    ∃ post,
      Ninst.RunCompiled concreteExitSevm concreteExitCallInput (.exec .call) post ∧
      post.stack = [1, 40] ∧ post.memory = concreteExitLoopMemory ∧
      post.gasLeft = 451107 ∧
      post.error = concreteExitCallInput.error ∧ post.output = concreteExitCallInput.output ∧
      post.returnData = [] ∧ post.logs = concreteExitCallInput.logs ∧
      post.refundCounter = concreteExitCallInput.refundCounter ∧
      post.accountsToDelete.isEmpty = concreteExitCallInput.accountsToDelete.isEmpty ∧
      ∃ stmid, concreteExitCallInput.state.subBal concreteCreateTarget 40 = some stmid ∧
        post.state = stmid.addBal concreteCreateSender 40 := by
  have hc : (concreteCreateSender.toB256).toAdr = concreteCreateSender := by decide +kernel
  have hext : (concreteExitCallInput.setMach
      ⟨[40], concreteExitCallInput.memory, concreteExitCallInput.gasLeft, concreteExitCallInput.stateGas⟩).extCost
      [(0, 0), (0, 0)] = 0 := by
    simp only [Devm.extCost, memExtsSize, memExtSize, if_true, Nat.sub_self]
  have hdel : accessDelegation concreteExitCallResolved concreteCreateSender =
      ⟨false, concreteCreateSender, ByteArray.empty, 0, concreteExitCallResolved⟩ := by
    rw [accessDelegation_of_not_delegation]
    · rw [concreteExitCallResolved_code]
    · rw [concreteExitCallResolved_code]
      decide +kernel
  have hempty : ¬ (concreteExitCallResolved.getAcct concreteCreateSender).Empty := by
    intro h
    have hb := h.2.2
    change concreteExitCallResolved.getBal concreteCreateSender = 0 at hb
    rw [concreteExitCallResolved_senderBalance] at hb
    exact (by decide +kernel : (999999999997823644 : B256) ≠ 0) hb
  have hsender : ¬ (concreteExitCallResolved.getAcct concreteExitSevm.currentTarget).bal < (40 : B256) := by
    change ¬ concreteExitCallResolved.getBal concreteCreateTarget < (40 : B256)
    rw [concreteExitCallResolved_targetBalance]
    decide +kernel
  have hh := Ninst.runCompiled_call_nonzero_codeFree
    (sevm := concreteExitSevm) (devm := concreteExitCallInput)
    (gw := 457907) (cw := concreteCreateSender.toB256) (vw := 40)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := [40])
    (dp := false) (dadr := concreteCreateSender) (code := ByteArray.empty) (dgc := 0)
    (d1 := concreteExitCallResolved) (ext := 0) (acc := 100) (create := 0)
    (mcc := 450895) (mcs := 444095)
    CoveredFork.prague rfl (by decide +kernel) hext
    (by
      simp only [hc, concreteExitCallInput, Devm.memory_setMach, Devm.gasLeft_setMach,
        Devm.setMach_setMach]
      exact hdel)
    (by rw [hc]; change accessCost concreteCreateSender concreteExitTotalBase.accessedAddresses + 0 = 100; exact concreteExitCall_warm)
    (by rw [hc, if_pos hempty])
    (by change calculateMsgCallGas 40 457907 457907 0 (100 + 0 + gasCallValue) = _; decide +kernel)
    (by change 450895 + 0 ≤ 457907; decide +kernel)
    rfl hsender (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)
  have hm0 (M : Mem) : M.extends [(0, 0), (0, 0)] = M := by cases M; rfl
  have hm : concreteExitCallInput.memory.extends [(0, 0), (0, 0)] = concreteExitLoopMemory := by
    rw [hm0]
    simp only [concreteExitCallInput, Devm.memory_setMach]
  have hg : concreteExitCallResolved.gasLeft - (450895 + 0) + 444095 = 451107 := rfl
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  simpa only [B256.toNat_zero, hm, hg, ht, hc] using hh

noncomputable def concreteExitCallPost : Devm := Classical.choose concreteExit_call_exists

theorem concreteExitCallPost_run :
    Ninst.RunCompiled concreteExitSevm concreteExitCallInput (.exec .call) concreteExitCallPost :=
  (Classical.choose_spec concreteExit_call_exists).1

private theorem concreteExitCallPost_machine :
    concreteExitCallPost.stack = [1, 40] ∧
    concreteExitCallPost.memory = concreteExitLoopMemory ∧
    concreteExitCallPost.gasLeft = 451107 := by
  have h := (Classical.choose_spec concreteExit_call_exists).2
  exact ⟨h.1, h.2.1, h.2.2.1⟩

private theorem concreteExitCallPost_meta :
    concreteExitCallPost.error = none ∧ concreteExitCallPost.logs = [] ∧
    concreteExitCallPost.refundCounter = 0 ∧ concreteExitCallPost.accountsToDelete.isEmpty = true := by
  have h := (Classical.choose_spec concreteExit_call_exists).2.2.2.2
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem concreteExitCallPost_transfer :
    ∃ stmid, concreteExitTotalBase.state.subBal concreteCreateTarget 40 = some stmid ∧
      concreteExitCallPost.state = stmid.addBal concreteCreateSender 40 :=
  (Classical.choose_spec concreteExit_call_exists).2.2.2.2.2.2.2.2.2.2

noncomputable def concreteExitRuntimePost : Devm :=
  (concreteExitCallPost.setMach
    ⟨[], concreteExitLoopMemory.write 0 (40 : B256).toBytes, 451083, concreteExitCallPost.stateGas⟩).withOutput (40 : B256).toBytes

private theorem concreteExit_afterCall (sevm : Sevm) (base : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[1, 40], M, G + 24, base.stateGas⟩)
      ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)
      ((base.setMach ⟨[], M.write 0 (40 : B256).toBytes, G, base.stateGas⟩).withOutput (40 : B256).toBytes) := by
  func_run (5) [0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  have hnsize : (M.write 0 (40 : B256).toBytes).size = 288 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
    exact hsize
  have hnread : ((M.write 0 (40 : B256).toBytes).read 0 32).1 = (40 : B256).toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M (ys := (40 : B256).toBytes) (by decide +kernel))
  have hnmem : ((M.write 0 (40 : B256).toBytes).read 0 32).2 = M.write 0 (40 : B256).toBytes := by
    apply Mem.read_snd_eq_self
    rw [hnsize]
    decide +kernel
  apply Func.runCompiled_return_of (G := G) (e := 0)
  · rfl
  · change calculateMemoryGasCost (memExtsSize (M.write 0 (40 : B256).toBytes).size [(0, 32)]) -
      calculateMemoryGasCost (M.write 0 (40 : B256).toBytes).size = 0
    rw [hnsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  · change (((M.write 0 (40 : B256).toBytes).read 0 32).1,
      base.setMach ⟨[], ((M.write 0 (40 : B256).toBytes).read 0 32).2, G, base.stateGas⟩) = _
    rw [hnread, hnmem]

private theorem concreteExit_callTail :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitTotalBase.setMach ⟨[40], concreteExitLoopMemory, 457925, concreteExitTotalBase.stateGas⟩)
      (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert))
      concreteExitRuntimePost := by
  have hprefix (sevm : Sevm) (base post : Devm) (M : Mem)
      (h : Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[457907, sevm.caller.toB256, 40, 0, 0, 0, 0, 40], M, 457907, base.stateGas⟩)
        (Ninst.call ::: ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post) :
      Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[40], M, 457925, base.stateGas⟩)
        (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post := by
    func_run (8)
    all_goals first
      | exact h
      | simp only [Devm.gasLeft_setMach, gVerylow, gBase]
  apply hprefix
  refine Func.RunCompiled.next (devm' := concreteExitCallPost) concreteExitCallPost_run ?_
  have heta (d : Devm) : d.setMach ⟨d.stack, d.memory, d.gasLeft, d.stateGas⟩ = d := by cases d; rfl
  have hm : concreteExitCallPost.setMach ⟨[1, 40], concreteExitLoopMemory, 451083 + 24, concreteExitCallPost.stateGas⟩ =
      concreteExitCallPost := by
    rw [← concreteExitCallPost_machine.1, ← concreteExitCallPost_machine.2.1]
    change concreteExitCallPost.setMach
      ⟨concreteExitCallPost.stack, concreteExitCallPost.memory, 451107, concreteExitCallPost.stateGas⟩ = concreteExitCallPost
    rw [← concreteExitCallPost_machine.2.2]
    exact heta _
  have h := concreteExit_afterCall concreteExitSevm concreteExitCallPost concreteExitLoopMemory
    451083 concreteExit_loopSize
  rw [hm] at h
  exact h

theorem concreteExit_runtime :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitDevm.setMach ⟨[], Mem.empty, 478795, concreteExitDevm.stateGas⟩) main concreteExitRuntimePost := by
  exact concreteExit_dispatch _ _ _ 478639 rfl rfl
    (concreteExit_prefix 457925 concreteExitRuntimePost concreteExit_callTail)

theorem concreteExitDevm_gas : concreteExitDevm.gasLeft = 478796 := by
  change 500000 - deploymentIntrinsicGas concreteExitTxInput concreteExitTx concreteCreateSender = 478796
  decide +kernel

theorem concreteExit_program :
    Prog.RunCompiled concreteExitSevm concreteExitDevm runtime concreteExitRuntimePost := by
  apply Prog.runCompiled_intro (G := 478795)
    (mid := concreteExitDevm.setMach ⟨[], Mem.empty, 478795, concreteExitDevm.stateGas⟩)
  · rw [concreteExitDevm_gas]
    decide
  · rfl
  exact concreteExit_runtime

theorem concreteExit_compiled : some concreteExitSevm.code.toList = Prog.compile runtime := by
  change some concreteExitMessage.code.toList = _
  rw [concreteExitMessage_code, code_compile]

theorem concreteExit_exec :
    exec (initEvm (concreteExitMessage.withBenv concreteExitEntry)) =
      .ok concreteExitRuntimePost :=
  Prog.exec_of_runCompiled concreteExit_program concreteExit_compiled

theorem concreteExit_frameEntry :
    (Frame.ofCall concreteExitMessage).enter =
      .run (initEvm (concreteExitMessage.withBenv concreteExitEntry)) := by
  have hnp : ¬ pragueRules.isPrecomp concreteCreateTarget :=
    concreteDeploymentBase.target_not_precompile (ChainConfig.pragueOnly_rulesAt 1 6)
  have he : executeCode.enter (concreteExitMessage.withBenv concreteExitEntry) =
      .inl (initEvm (concreteExitMessage.withBenv concreteExitEntry)) := by
    unfold executeCode.enter
    change (if !false && pragueRules.isPrecomp concreteCreateTarget then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, hnp]
    rfl
  unfold Frame.enter Frame.ofCall
  rw [concreteExitEntry_run]
  dsimp only
  rw [he]

private theorem concreteExit_postError : concreteExitRuntimePost.error = none :=
  concreteExitCallPost_meta.1

theorem concreteExit_processMessage :
    processMessage concreteExitMessage = .ok concreteExitRuntimePost := by
  unfold processMessage runFrame
  rw [concreteExit_frameEntry]
  simp [Frame.settle_eq_settleMsg_handleErrorWith, Frame.settleMsg, concreteExit_exec,
    executeCode.handleErrorWith_ok, Frame.ofCall, processMessage.settle, concreteExit_postError]

noncomputable def concreteExitMessageState : State := concreteExitRuntimePost.state

noncomputable def concreteExitMessageOutput : MsgCallOutput := {
  gasLeft := 451083
  refundCounter := 0
  logs := []
  accountsToDelete := concreteExitCallPost.accountsToDelete
  error := none
  returnData := (40 : B256).toBytes }

theorem concreteExit_messageCall :
    processMessageCall concreteExitMessage = .ok (concreteExitMessageState, concreteExitMessageOutput) := by
  have htarget : concreteExitMessage.target.isNone = false := rfl
  have hauths : concreteExitMessage.tenv.stat.auths = [] := rfl
  have hcode : some concreteExitMessage.code.toList = Prog.compile runtime := concreteExit_compiled
  have hdelegation : getDelegatedCodeAddress concreteExitMessage.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcode)]
  have hrefund : concreteExitRuntimePost.refundCounter = 0 := concreteExitCallPost_meta.2.2.1
  have hlogs : concreteExitRuntimePost.logs = [] := concreteExitCallPost_meta.2.1
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind, hdelegation,
    concreteExit_processMessage, Except.bimap, id_eq, concreteExit_postError,
    Option.isNone, hrefund]
  simp only [concreteExitRuntimePost, Devm.withOutput_logs, Devm.setMach_logs,
    concreteExitCallPost_meta.2.1]
  rfl

noncomputable def concreteExitTransactionState : State :=
  deploymentFinalState concreteExitTxInput concreteExitTx concreteCreateSender
    concreteExitMessageState 48917

noncomputable def concreteExitTransactionBout : BlockOutput :=
  deploymentFinalBout .init concreteExitTx 0 concreteExitMessageOutput 48917

theorem concreteExit_transaction :
    processTransaction concreteExitTxInput .init concreteExitTx 0 =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
  have hchecked := concreteExitChecked
  change checkTransaction concreteExitTxInput.beginTransaction
    (deploymentTxPreludeBout .init concreteExitTx 0) concreteExitTx =
      .ok (concreteCreateSender, 2, [], 0) at hchecked
  have hdebit := concreteExitDebit_run
  simp only [Benv.beginTransaction] at hdebit
  have hprepareRun :
      Except.bind
        (prepareMessage
          { concreteExitTxInput.beginTransaction with state := concreteExitDebit }
          concreteExitTenv concreteExitTx)
        (fun msg => Except.mapError TransitionError.vm (processMessageCall msg)) =
        .ok (concreteExitMessageState, concreteExitMessageOutput) := by
    rw [concreteExitMessage_prepared]
    simp only [Except.bind, concreteExit_messageCall, Except.mapError]
  have hvalidationStateGas :
      concreteExitTxInput.beginTransaction.stat.rules.stateGas = none := by
    change concreteExitTxInput.stat.rules.stateGas = none
    exact CoveredFork.prague.rules_stateGas_none
  have hforkStateGas : pragueRules.stateGas = none := pragueRules_stateGas
  have hrules : concreteExitTxInput.beginTransaction.stat.rules = pragueRules := rfl
  have htypeThree : concreteExitTx.isTypeThree = false := rfl
  have haccessList : concreteExitTx.accessList = [] := rfl
  have hauths : concreteExitTx.auths = [] := rfl
  unfold processTransaction
  simp only [bind, Except.bind]
  change (do
    let validationSender ←
      ((match concreteExitTxInput.beginTransaction.stat.rules.stateGas with
        | none => Except.ok 0
        | some _ => do
          Except.mapError TransitionError.transaction
            (checkTransactionChainId concreteExitTxInput.beginTransaction concreteExitTx)
          Except.mapError (fun e => TransitionError.senderRecovery e)
            (recoverSender concreteExitTxInput.beginTransaction.stat.chainId concreteExitTx)) :
        Except TransitionError Adr)
    (fun _ => _) validationSender) =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) <;>
  rw [hvalidationStateGas]
  simp only [bind, Except.bind]
  rw [hrules]
  simp only [Except.mapError]
  simp only [deploymentTxPreludeBout, ExecutionTrace.transactionPreludeBout] at hchecked
  rw [hchecked]
  simp only [htypeThree, haccessList, hauths, Bool.false_eq_true, if_false,
    Nat.add_zero, Benv.beginTransaction]
  have htxGas : concreteExitTx.gas = 500000 := rfl
  rw [htxGas, show Nat.toB256 (500000 * 2) = 1000000 by decide +kernel, hdebit]
  simp only [Option.toExcept]
  change (Except.bind
    (Except.bind
      (prepareMessage
        {concreteExitTxInput.beginTransaction with state := concreteExitDebit}
        concreteExitTenv concreteExitTx)
      (fun msg => Except.mapError TransitionError.vm (processMessageCall msg)))
    (fun v => _)) = _
  rw [hprepareRun]
  simp only [Except.bind]
  have hprice : min 1 (8 - concreteExitTxInput.stat.baseFeePerGas) +
      concreteExitTxInput.stat.baseFeePerGas = 2 := by rfl
  have hgas : max (500000 - 451083 - min ((500000 - 451083) / 5) 0)
      (calculateIntrinsicCost pragueRules concreteExitTx concreteCreateSender).2 = 48917 := by decide +kernel
  unfold concreteExitMessageOutput
  rw [show Int.toNat? 0 = some 0 by rfl]
  simp only [hgas]
  unfold concreteExitTransactionState concreteExitTransactionBout deploymentFinalState deploymentFinalBout
  simp only [deploymentEffectiveGasPrice, concreteExitTx, concreteExitMessageOutput, hprice]
  have hdelete : concreteExitCallPost.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact concreteExitCallPost_meta.2.2.2
  rw [hdelete]
  rfl


/-- The selected actual child state has paid forty out of the funded four-store parent. -/
theorem concreteExitMessageState_paid :
    concreteExitMessageState = (concreteExitTotalBase.state.setBal concreteCreateTarget 60).addBal
      concreteCreateSender 40 := by
  obtain ⟨mid, hsub, hpost⟩ := concreteExitCallPost_transfer
  have hm := (State.of_subBal hsub).2
  have hb : concreteExitTotalBase.state.bal concreteCreateTarget = 100 := concreteExitTotalBase_balance
  change concreteExitCallPost.state = _
  rw [hpost, hm, hb, show (100 : B256) - 40 = 60 by decide +kernel]

theorem concreteExitTransactionCode (a : Adr) :
    concreteExitTransactionState.getCode a = concreteDripped.state.getCode a := by
  unfold concreteExitTransactionState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode, concreteExitMessageState_paid,
    State.addBal_getCode, State.setBal_getCode]
  exact concreteExitTotalBase_code a

theorem concreteExit_receiptEntry :
    concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]? =
      some (makeReceipt concreteExitTx none 48917 []) := by
  change (BlockOutput.init.receiptsTrie.insert (deploymentReceiptKey 0)
    (makeReceipt concreteExitTx none 48917 []))[deploymentReceiptKey 0]? = _
  rw [Std.TreeMap.getElem?_insert_self]

theorem concreteExit_requestSuffix :
    processGeneralPurposeRequests (concreteExitTxInput.withState concreteExitTransactionState)
      concreteExitTransactionBout = .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
  have hcode (a : Adr) (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
      some (concreteExitTransactionState.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [concreteExitTransactionCode]
    rw [concreteDrippedCode, concreteJoinedCode]
    exact concreteDeployedSystemCode a ha
  obtain ⟨withdrawalOut, hw, _, _, _, _, hwr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (concreteExitTxInput.withState concreteExitTransactionState) withdrawalRequestPredeployAddress []
      (hcode _ (by simp)) (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
      CoveredFork.prague
  obtain ⟨consolidationOut, hc, _, _, _, _, hcr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((concreteExitTxInput.withState concreteExitTransactionState).withState concreteExitTransactionState)
      consolidationRequestPredeployAddress [] (hcode _ (by simp))
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide) CoveredFork.prague
  have hrequests :
      (concreteExitTxInput.withState concreteExitTransactionState).stat.rules.requests =
        [(1, withdrawalRequestPredeployAddress),
         (2, consolidationRequestPredeployAddress)] := by
    change pragueRules.requests = _
    exact pragueRules_requests
  have hw' : processCheckedSystemTransaction
      (concreteExitTxInput.withState concreteExitTransactionState)
      withdrawalRequestPredeployAddress [] =
      .ok (concreteExitTransactionState, withdrawalOut) := by
    simpa [Benv.withState] using hw
  have hbalNone :
      (concreteExitTxInput.withState concreteExitTransactionState).stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  have hbaseBalNone : concreteExitTxInput.stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  have hd : parseDepositRequests concreteExitTransactionBout = .ok [] := by
    unfold parseDepositRequests
    have hk : concreteExitTransactionBout.receiptKeys = [deploymentReceiptKey 0] := rfl
    rw [hk]
    simp
    rw [concreteExit_receiptEntry]
    unfold makeReceipt
    rfl
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
  rw [hd, hrequests]
  simp [runRequestContracts, hw', hc, hwr, hcr, hbalNone, hbaseBalNone]
  rfl

theorem concreteExit_body :
    applyBody concreteExitTxInput [.inl concreteExitTxRlp] [] =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
  obtain ⟨beaconOut, hb, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    concreteExitTxInput beaconRootsAddress concreteExitTxInput.stat.parentBeaconBlockRoot.toBytes
    (by change some (concreteDripped.state.getCode _).toList = _
        rw [concreteDrippedCode, concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp beaconRootsAddress; decide) CoveredFork.prague
  obtain ⟨historyOut, hh, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (concreteExitTxInput.withState concreteDripped.state) historyStorageAddress
    concreteDripBlock.header.hash.toBytes
    (by change some (concreteDripped.state.getCode _).toList = _
        rw [concreteDrippedCode, concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp historyStorageAddress; decide) CoveredFork.prague
  have hl : (concreteExitTxInput.withState concreteDripped.state).stat.blockHashes.getLast? =
      some concreteDripBlock.header.hash := by rfl
  have hi : (concreteExitTxInput.withState concreteDripped.state).withState concreteDripped.state =
      concreteExitTxInput := rfl
  have hstate : concreteExitTxInput.state = concreteDripped.state := rfl
  have hh' : processUncheckedSystemTransaction
      (concreteExitTxInput.withState concreteExitTxInput.state) historyStorageAddress
      concreteDripBlock.header.hash.toBytes =
      .ok ((concreteExitTxInput.withState concreteExitTxInput.state).state, historyOut) := by
    simpa only [hstate] using hh
  have hl' : (concreteExitTxInput.withState concreteExitTxInput.state).stat.blockHashes.getLast? =
      some concreteDripBlock.header.hash := by
    simpa only [hstate] using hl
  have hi' : (concreteExitTxInput.withState concreteExitTxInput.state).withState
      concreteExitTxInput.state = concreteExitTxInput := by
    simpa only [hstate] using hi
  have hbalNone : concreteExitTxInput.stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  unfold applyBody
  simp only [BalBuilder.incorporateSystem, hbalNone, checkBlockAccessListGasLimit]
  rw [hb]
  simp only [Except.mapError, bind, Except.bind]
  rw [hl']
  simp only [Option.toExcept, hh', Except.mapError, bind, Except.bind]
  rw [show (concreteExitTxInput.withState concreteExitTxInput.state).state =
    concreteExitTxInput.state from rfl, hi']
  have htransaction := concreteExit_transaction
  unfold BlockOutput.init at htransaction
  simp only [BlockOutput.init, List.mapM_cons, List.mapM_nil, concreteExitDecode, pure, Except.pure, bind, Except.bind, List.putIndex, List.putIndex.aux,
    applyTransactions, htransaction]
  have hwithdrawals : processWithdrawals
      (concreteExitTxInput.withState concreteExitTransactionState)
      concreteExitTransactionBout [] =
      (concreteExitTransactionState, concreteExitTransactionBout) := by
    unfold processWithdrawals processWithdrawalsState processWithdrawalsTrie
      BlockOutput.withWithdrawalsTrie
    rfl
  rw [hwithdrawals]
  simp only [Prod.fst, Prod.snd]
  have hws (b : Benv) (st : State) : (b.withState st).withState st = b.withState st := rfl
  rw [hws]
  rw [concreteExit_requestSuffix]
  rfl

noncomputable def concreteExitHeader (sr tr rr wr rh : B256) : Header :=
  { concreteExitExecutionHeader with
    gasUsed := 48917
    stateRoot := sr
    txsRoot := tr
    receiptRoot := rr
    withdrawalsRoot := wr
    requestsHash := some rh }

theorem concreteExitHeader_benv (sr tr rr wr rh : B256) :
    initBenv .prague concreteDripped (concreteExitHeader sr tr rr wr rh) = concreteExitTxInput := rfl

theorem concreteExitHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteDripped (concreteExitHeader sr tr rr wr rh) = .ok () := by
  have hlast : concreteDripped.blocks.getLast? = some concreteDripBlock :=
    appendBlock_getLast? concreteJoined.blocks concreteDripBlock
  have hDeploy : concreteDeploymentEnvelope.block.header =
      concreteDeploymentHeader concreteDeploymentBody.1.root
        (getTransactionsRoot concreteDeploymentBody.2) (getReceiptRoot concreteDeploymentBody.2)
        (getWithdrawalsRoot concreteDeploymentBody.2)
        (computeRequestsHash concreteDeploymentBody.2.requests) := rfl
  have hJoin : concreteJoinBlock.header =
      concreteJoinHeader concreteJoinTransactionState.root
        (getTransactionsRoot concreteJoinTransactionBout) (getReceiptRoot concreteJoinTransactionBout)
        (getWithdrawalsRoot concreteJoinTransactionBout)
        (computeRequestsHash concreteJoinTransactionBout.requests) := rfl
  have hDrip : concreteDripBlock.header =
      concreteDripHeader concreteDripTransactionState.root
        (getTransactionsRoot concreteDripTransactionBout) (getReceiptRoot concreteDripTransactionBout)
        (getWithdrawalsRoot concreteDripTransactionBout)
        (computeRequestsHash concreteDripTransactionBout.requests) := rfl
  have hparentGasLimit : concreteDripBlock.header.gasLimit = 10000000 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentGasUsed : concreteDripBlock.header.gasUsed = 32075 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentBaseFee : concreteDripBlock.header.baseFeePerGas = 1 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentTimestamp : concreteDripBlock.header.timestamp = 5 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentNumber : concreteDripBlock.header.number = 3 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentBlobGas : concreteDripBlock.header.blobGasUsed = 0 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentExcessBlobGas : concreteDripBlock.header.excessBlobGas = 0 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentExtraData : concreteDripBlock.header.extraData = [] := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentDifficulty : concreteDripBlock.header.difficulty = 0 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentNonce : concreteDripBlock.header.nonce = 0 := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentOmmers : concreteDripBlock.header.ommersHash = emptyOmmerHash := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentBal : concreteDripBlock.header.blockAccessListHash = none := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hparentSlot : concreteDripBlock.header.slotNumber = none := by
    simp only [hDrip, concreteDripHeader, concreteDripExecutionHeader, hJoin, concreteJoinHeader, concreteJoinExecutionHeader, hDeploy, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader] <;> rfl
  have hbase : calculateBaseFeePerGas 10000000 10000000 32075 1 = .ok 1 := by
    decide +kernel
  have hexcess : calculateExcessBlobGas pragueRules.blob concreteDripBlock.header = 0 := by
    unfold calculateExcessBlobGas
    rw [hparentExcessBlobGas, hparentBlobGas]
    decide +kernel
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind,
    concreteExitHeader, concreteExitExecutionHeader, Header.hash, hparentGasLimit, hparentGasUsed, hparentBaseFee, hparentTimestamp, hparentNumber, hparentBlobGas, hparentExcessBlobGas, hparentExtraData, hparentDifficulty, hparentNonce, hparentOmmers, hparentBal, hparentSlot,
    hbase, hexcess, ne_eq, not_true_eq_false, ite_false]
  simp only [Except.mapError]
  rfl

noncomputable def concreteExitBlock : Block := {
  header := concreteExitHeader concreteExitTransactionState.root
    (getTransactionsRoot concreteExitTransactionBout) (getReceiptRoot concreteExitTransactionBout)
    (getWithdrawalsRoot concreteExitTransactionBout) (computeRequestsHash concreteExitTransactionBout.requests)
  txs := [.inl concreteExitTxRlp]
  ommers := []
  wds := [] }

noncomputable def concreteExited : BlockChain :=
  ⟨appendBlock concreteDripped.blocks concreteExitBlock, concreteExitTransactionState, concreteDripped.chainId⟩

theorem concreteExit_checks :
    stateTransitionChecks concreteExitTransactionBout concreteExitBlock.header
      (getTransactionsRoot concreteExitTransactionBout) concreteExitTransactionState.root
      (getReceiptRoot concreteExitTransactionBout) (logsBloom concreteExitTransactionBout.blockLogs)
      (getWithdrawalsRoot concreteExitTransactionBout)
      (computeRequestsHash concreteExitTransactionBout.requests) = .ok () := by
  have hg : concreteExitTransactionBout.blockGasUsed = 48917 := rfl
  have hl : concreteExitTransactionBout.blockLogs = [] := rfl
  have hb : concreteExitTransactionBout.blobGasUsed = 0 := rfl
  simp only [stateTransitionChecks, hg, hl, hb, concreteExitBlock, concreteExitHeader,
    concreteExitExecutionHeader, concreteDripBlock, concreteDripHeader, concreteDripExecutionHeader, concreteJoinBlock, concreteJoinHeader, concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteExit_step :
    stateTransitionUsing concreteConfig concreteDripped concreteExitBlock = .ok concreteExited := by
  have hchain : concreteConfig.chainId = concreteDripped.chainId := concreteDeploymentRoot.deployed_chainId
  rw [stateTransitionUsing_eq_of_chainId_eq hchain]
  rw [show concreteConfig.forkAt concreteExitBlock.header.timestamp = .ok .prague from
    ChainConfig.pragueOnly_forkAt 1 _]
  change stateTransitionAt .prague concreteDripped concreteExitBlock = _
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE]
  have hh : validateHeader Fork.prague.ruleSet concreteDripped concreteExitBlock.header = .ok () := by
    change validateHeader pragueRules concreteDripped concreteExitBlock.header = .ok ()
    exact concreteExitHeader_valid _ _ _ _ _
  rw [hh]
  change (do
    let output ← applyBody (initBenv .prague concreteDripped concreteExitBlock.header)
      concreteExitBlock.txs concreteExitBlock.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteExitBlock.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs)
      (getWithdrawalsRoot output.2) (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteDripped.blocks concreteExitBlock, output.1,
      concreteDripped.chainId⟩ : BlockChain)) = .ok concreteExited
  have hbody : applyBody (initBenv .prague concreteDripped concreteExitBlock.header)
      concreteExitBlock.txs concreteExitBlock.wds =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
    change applyBody (initBenv .prague concreteDripped (concreteExitHeader _ _ _ _ _))
      [.inl concreteExitTxRlp] [] = _
    rw [concreteExitHeader_benv]
    exact concreteExit_body
  rw [hbody]
  simp only [Bind.bind, Except.bind, concreteExit_checks, Except.mapError]
  rfl


theorem concreteExited_storage : concreteExited.state.getStor concreteCreateTarget =
    ((((concreteDripped.state.getStor concreteCreateTarget).set chiSlot concreteExitChi).set rhoSlot 6).set
      concreteCreateSender.toB256 59).set totalUnitsSlot 59 := by
  change concreteExitTransactionState.getStor concreteCreateTarget = _
  unfold concreteExitTransactionState deploymentFinalState State.getStor State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor, concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_stor]
  exact concreteExitTotalBase_storage

theorem concreteExited_values :
    (concreteExited.state.getStor concreteCreateTarget).get chiSlot = concreteExitChi ∧
    (concreteExited.state.getStor concreteCreateTarget).get rhoSlot = 6 ∧
    (concreteExited.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 59 ∧
    (concreteExited.state.getStor concreteCreateTarget).get totalUnitsSlot = 59 := by
  rw [concreteExited_storage]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel),
      Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  · exact Stor.get_set_self _ _ _

theorem concreteExitedTargetBalance : concreteExited.state.bal concreteCreateTarget = 60 := by
  change (concreteExitTransactionState.get concreteCreateTarget).bal = _
  unfold concreteExitTransactionState deploymentFinalState
  change (((concreteExitMessageState.addBal concreteCreateSender 902166).addBal 0 48917).get
    concreteCreateTarget).bal = _
  have hz : (0 : Adr) ≠ concreteCreateTarget := by decide +kernel
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_ne ht]
  rw [concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self, Acct.withBal]

theorem concreteExitedSenderBalance :
    concreteExited.state.bal concreteCreateSender = 999999999998725850 := by
  change (concreteExitTransactionState.get concreteCreateSender).bal = _
  unfold concreteExitTransactionState deploymentFinalState
  change (((concreteExitMessageState.addBal concreteCreateSender 902166).addBal 0 48917).get
    concreteCreateSender).bal = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_self, Acct.withBal,
    State.bal, State.setBal_get_ne ht]
  change (concreteExitTotalBase.getBal concreteCreateSender + 40) + 902166 = _
  rw [concreteExitTotalBase_senderBalance]
  decide +kernel

private theorem concreteExitTotalBase_sender :
    concreteExitTotalBase.state.get concreteCreateSender = concreteExitEntry.state.get concreteCreateSender := by
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  change (((((concreteExitEntry.state.setStorVal concreteCreateTarget chiSlot concreteExitChi).setStorVal
    concreteCreateTarget rhoSlot 6).setStorVal concreteCreateTarget concreteCreateSender.toB256 59).setStorVal
    concreteCreateTarget totalUnitsSlot 59).get concreteCreateSender) = _
  simp only [State.setStorVal, State.get_set_ne _ ht]

theorem concreteExitedSenderNonce : concreteExited.state.getNonce concreteCreateSender = 4 := by
  change (concreteExitTransactionState.get concreteCreateSender).nonce = _
  unfold concreteExitTransactionState deploymentFinalState
  change (((concreteExitMessageState.addBal concreteCreateSender 902166).addBal 0 48917).get
    concreteCreateSender).nonce = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  rw [concreteExitTotalBase_sender]
  change ((((concreteExitDebit.setBal concreteCreateSender
    (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateSender).nonce) = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  unfold concreteExitDebit
  simp only [State.setBal_get_self, State.incrNonce, State.get_set_self]
  change (concreteDripped.state.getNonce concreteCreateSender) + 1 = 4
  rw [concreteDrippedSenderNonce]
  rfl

theorem concreteExit_receiptSucceeded :
    (concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true := by
  rw [concreteExit_receiptEntry]
  rfl

theorem concreteExit_observations :
    concreteExitMessageOutput.returnData = (40 : B256).toBytes ∧
    concreteExitTransactionBout.blockGasUsed = 48917 ∧
    concreteExitTransactionBout.blockLogs = [] ∧
    concreteExitBlock.header.timestamp = 6 ∧ concreteExitBlock.header.number = 4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One actual configured exit block, its funded child payment, and its observable accounting. -/
theorem concreteExit_checkpoint :
    stateTransitionUsing concreteConfig concreteDripped concreteExitBlock = .ok concreteExited ∧
    concreteExitMessageState = (concreteExitTotalBase.state.setBal concreteCreateTarget 60).addBal
      concreteCreateSender 40 ∧
    concreteExited.state.getStor concreteCreateTarget =
      ((((concreteDripped.state.getStor concreteCreateTarget).set chiSlot concreteExitChi).set rhoSlot 6).set
        concreteCreateSender.toB256 59).set totalUnitsSlot 59 ∧
    ((concreteExited.state.getStor concreteCreateTarget).get chiSlot = concreteExitChi ∧
      (concreteExited.state.getStor concreteCreateTarget).get rhoSlot = 6 ∧
      (concreteExited.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 59 ∧
      (concreteExited.state.getStor concreteCreateTarget).get totalUnitsSlot = 59) ∧
    concreteExited.state.bal concreteCreateTarget = 60 ∧
    concreteExited.state.bal concreteCreateSender = 999999999998725850 ∧
    concreteExited.state.getNonce concreteCreateSender = 4 ∧
    (concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true ∧
    (concreteExitMessageOutput.returnData = (40 : B256).toBytes ∧
      concreteExitTransactionBout.blockGasUsed = 48917 ∧
      concreteExitTransactionBout.blockLogs = [] ∧
      concreteExitBlock.header.timestamp = 6 ∧ concreteExitBlock.header.number = 4) :=
  ⟨concreteExit_step, concreteExitMessageState_paid, concreteExited_storage, concreteExited_values,
    concreteExitedTargetBalance, concreteExitedSenderBalance, concreteExitedSenderNonce,
    concreteExit_receiptSucceeded, concreteExit_observations⟩

end Drip
end Blanc
