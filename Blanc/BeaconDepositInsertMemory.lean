import Blanc.BeaconDepositReconstruct

/-!
# Beacon deposit insertion memory carriers

After deposit-data reconstruction, insertion needs only the old count, shifted
count, and current node registers.  This leaf forgets the spent reconstruction
inputs and carries exactly those three words through pair staging and shifts.
-/

namespace Blanc.BeaconDeposit

open Jaune

private lemma Bytes.sliceD_writeAt_after_insert
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt, if_neg]
  omega

private lemma Bytes.sliceD_stagedPair_insert
    (image : Bytes) (left right : B256) :
    (Bytes.writeAt
      (Bytes.writeAt image 0 left.toBytes) 32 right.toBytes).sliceD
        0 64 0 = left.toBytes ++ right.toBytes := by
  have hleft : left.toBytes.length = 32 := B256.length_toBytes left
  have hright : right.toBytes.length = 32 := B256.length_toBytes right
  have hfirst : Bytes.writeAt image 0 left.toBytes =
      left.toBytes ++ image.drop 32 := by
    rw [Bytes.writeAt, hleft, show List.takeD 0 image 0 = [] from rfl,
      List.nil_append, Nat.zero_add]
  have hsecond :
      Bytes.writeAt (left.toBytes ++ image.drop 32) 32 right.toBytes =
        left.toBytes ++ (right.toBytes ++ (image.drop 32).drop 32) := by
    rw [Bytes.writeAt, hright, List.takeD_eq_take _ (by simp [hleft]),
      List.take_left' hleft,
      show 32 + 32 = left.toBytes.length + 32 by rw [hleft],
      List.drop_append, List.append_assoc]
    simp [hleft]
  rw [hfirst, hsecond]
  unfold List.sliceD
  rw [List.drop_zero,
    List.takeD_eq_take _ (by simp [hleft, hright]; omega),
    ← List.append_assoc, List.take_left' (by simp [hleft, hright])]

/-- The 768-byte register image used by the insertion loop. -/
structure InsertionMemoryCarrier
    (memory : Mem) (oldCount shiftedSize node : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 768
  oldCount_read : image.sliceD 576 32 0 = oldCount.toBytes
  shiftedSize_read : image.sliceD 608 32 0 = shiftedSize.toBytes
  node_read : image.sliceD 640 32 0 = node.toBytes

/-- The same insertion image after staging one branch/node SHA pair. -/
structure InsertionPairMemoryCarrier
    (memory : Mem) (oldCount shiftedSize left right : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 768
  oldCount_read : image.sliceD 576 32 0 = oldCount.toBytes
  shiftedSize_read : image.sliceD 608 32 0 = shiftedSize.toBytes
  shaInput : memory.data.sliceD 0 64 0 = left.toBytes ++ right.toBytes

theorem InsertionMemoryCarrier.readOldCount
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : InsertionMemoryCarrier memory oldCount shiftedSize node) :
    Bytes.toB256 (memory.read 576 32).1 = oldCount := by
  rw [Mem.Reads.read h.reads, h.oldCount_read, B256.toB256_toBytes]

theorem InsertionMemoryCarrier.readShiftedSize
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : InsertionMemoryCarrier memory oldCount shiftedSize node) :
    Bytes.toB256 (memory.read 608 32).1 = shiftedSize := by
  rw [Mem.Reads.read h.reads, h.shiftedSize_read, B256.toB256_toBytes]

theorem InsertionMemoryCarrier.readNode
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : InsertionMemoryCarrier memory oldCount shiftedSize node) :
    Bytes.toB256 (memory.read 640 32).1 = node := by
  rw [Mem.Reads.read h.reads, h.node_read, B256.toB256_toBytes]

/-- The final reconstruction image becomes the first insertion image after
the incremented count is staged in word 19. -/
def ReconstructRegistersMemoryCarrier.startInsertion
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second shiftedSize : B256}
    (h : ReconstructRegistersMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node intermediate
      second 768) :
    InsertionMemoryCarrier (memory.write 608 shiftedSize.toBytes)
      oldCount shiftedSize node := by
  let source := h.intermediate.node.source
  let image := Bytes.writeAt source.image 608 shiftedSize.toBytes
  refine ⟨image, source.wf.write _ _, Mem.Reads.write source.wf source.reads _ _,
    ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, source.size_eq]
      omega), source.size_eq]
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_before]
    exact source.oldCount_read
    omega
  · dsimp only [image]
    rw [show 32 = shiftedSize.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    exact h.intermediate.node.node_read

/-- A covered write below the register bank preserves all three insertion
words. -/
def InsertionMemoryCarrier.writeBeforeRegisters
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (n : Nat) (xs : Bytes)
    (hbefore : n + xs.length ≤ 576)
    (hfit : n + xs.length ≤ 768) :
    InsertionMemoryCarrier (memory.write n xs)
      oldCount shiftedSize node := by
  let image := Bytes.writeAt h.image n xs
  refine ⟨image, h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _,
    ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by rw [h.size_eq]; exact hfit), h.size_eq]
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ hbefore]
    exact h.oldCount_read
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by omega)]
    exact h.shiftedSize_read
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by omega)]
    exact h.node_read

/-- Replace the shifted-count register while preserving old count and node. -/
def InsertionMemoryCarrier.writeShiftedSize
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (shiftedSize' : B256) :
    InsertionMemoryCarrier (memory.write 608 shiftedSize'.toBytes)
      oldCount shiftedSize' node := by
  let image := Bytes.writeAt h.image 608 shiftedSize'.toBytes
  refine ⟨image, h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _,
    ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]
      omega), h.size_eq]
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_before]
    exact h.oldCount_read
    omega
  · dsimp only [image]
    rw [show 32 = shiftedSize'.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    exact h.node_read

/-- Stage the branch word and current node as the next 64-byte SHA input. -/
def InsertionMemoryCarrier.stagePair
    {memory : Mem} {oldCount shiftedSize node left : B256}
    (h : InsertionMemoryCarrier memory oldCount shiftedSize node) :
    InsertionPairMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 node.toBytes)
      oldCount shiftedSize left node := by
  let M1 := memory.write 0 left.toBytes
  let I1 := Bytes.writeAt h.image 0 left.toBytes
  let M2 := M1.write 32 node.toBytes
  let I2 := Bytes.writeAt I1 32 node.toBytes
  have hwf1 : Mem.Wf M1 := h.wf.write _ _
  have hreads1 : Mem.Reads M1 I1 := Mem.Reads.write h.wf h.reads _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hreads2 : Mem.Reads M2 I2 := Mem.Reads.write hwf1 hreads1 _ _
  have hsize1 : M1.size = 768 := by
    dsimp only [M1]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]
      omega), h.size_eq]
  have hsize2 : M2.size = 768 := by
    dsimp only [M2]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hsize1]
      omega), hsize1]
  have hold : I2.sliceD 576 32 0 = oldCount.toBytes := by
    dsimp only [I2]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    dsimp only [I1]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    exact h.oldCount_read
  have hshift : I2.sliceD 608 32 0 = shiftedSize.toBytes := by
    dsimp only [I2]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    dsimp only [I1]
    rw [Bytes.sliceD_writeAt_after_insert _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    exact h.shiftedSize_read
  have hpairImage : I2.sliceD 0 64 0 = left.toBytes ++ node.toBytes := by
    exact Bytes.sliceD_stagedPair_insert h.image left node
  have hsha := Mem.Reads.read hreads2 0 64
  change M2.data.sliceD 0 64 0 = I2.sliceD 0 64 0 at hsha
  rw [hpairImage] at hsha
  exact ⟨I2, hwf2, hreads2, hsize2, hold, hshift, hsha⟩

/-- Write the staged pair's digest back into the current-node register. -/
def InsertionPairMemoryCarrier.finishHash
    {memory : Mem} {oldCount shiftedSize left right : B256}
    (h : InsertionPairMemoryCarrier memory oldCount shiftedSize left right) :
    InsertionMemoryCarrier
      (memory.write 640 (hashPair Bytes.sha256 left right).toBytes)
      oldCount shiftedSize (hashPair Bytes.sha256 left right) := by
  let digest := hashPair Bytes.sha256 left right
  let image := Bytes.writeAt h.image 640 digest.toBytes
  refine ⟨image, h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _,
    ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]
      omega), h.size_eq]
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_before]
    exact h.oldCount_read
    omega
  · dsimp only [image]
    rw [Bytes.sliceD_writeAt_before]
    exact h.shiftedSize_read
    omega
  · dsimp only [image]
    rw [show 32 = digest.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _

end Blanc.BeaconDeposit
