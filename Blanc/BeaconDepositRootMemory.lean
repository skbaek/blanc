import Blanc.BeaconDepositSha

/-!
# Beacon deposit root-fold memory carriers

Contract-local symbolic images for the `get_deposit_root` fold.  The live and
dead arms both stage one 64-byte SHA-256 input at the bottom of the runtime's
672-byte register image, while the count, shifted size, and current node remain
available in words 18, 19, and 20.
-/

namespace Blanc.BeaconDeposit

open Jaune

private lemma Bytes.length_writeAt
    (bs : Bytes) (n : Nat) (xs : Bytes) :
    (Bytes.writeAt bs n xs).length = max bs.length (n + xs.length) := by
  simp only [Bytes.writeAt, List.length_append, List.takeD_length,
    List.length_drop]
  omega

private lemma Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [if_neg]
  omega

private lemma Bytes.sliceD_stagedPair
    (image : Bytes) (left right : B256) :
    (Bytes.writeAt
      (Bytes.writeAt image 0 left.toBytes) 32 right.toBytes).sliceD
        0 64 0 = left.toBytes ++ right.toBytes := by
  rw [List.sliceD_eq_map]
  apply List.ext_get
  · simp only [List.length_map, List.length_range, List.length_append,
      B256.length_toBytes]
  · intro i hi₁ hi₂
    simp only [List.length_map, List.length_range] at hi₁
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
      zero_add]
    by_cases hi : i < 32
    · rw [Bytes.getD_writeAt, if_neg (by omega),
        Bytes.getD_writeAt, if_pos (by
          simp only [B256.length_toBytes]
          omega)]
      rw [List.getElem_append_left (by
        simpa only [B256.length_toBytes] using hi)]
      rw [Nat.sub_zero, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by
          simpa only [B256.length_toBytes] using hi)]
      rfl
    · have hi32 : 32 ≤ i := Nat.not_lt.mp hi
      have hi64 : i < 64 := hi₁
      have hir : i - 32 < right.toBytes.length := by
        rw [B256.length_toBytes]
        omega
      rw [Bytes.getD_writeAt, if_pos (by
        simp only [B256.length_toBytes]
        omega)]
      rw [List.getElem_append_right (by
        simp only [B256.length_toBytes]
        omega)]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hir]
      simp only [B256.length_toBytes]
      rfl

/-- The three persistent register words used throughout the root fold. -/
structure RootMemoryCarrier
    (memory : Mem) (oldCount shiftedSize node : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 672
  image_length : image.length = 672
  oldCount_read : image.sliceD 576 32 0 = oldCount.toBytes
  shiftedSize_read : image.sliceD 608 32 0 = shiftedSize.toBytes
  node_read : image.sliceD 640 32 0 = node.toBytes

/-- The same register image after staging a 64-byte SHA-256 input. -/
structure RootPairMemoryCarrier
    (memory : Mem) (oldCount shiftedSize left right : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 672
  image_length : image.length = 672
  oldCount_read : image.sliceD 576 32 0 = oldCount.toBytes
  shiftedSize_read : image.sliceD 608 32 0 = shiftedSize.toBytes
  shaInput :
    memory.data.sliceD 0 64 0 = left.toBytes ++ right.toBytes

theorem RootMemoryCarrier.read_oldCount
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : RootMemoryCarrier memory oldCount shiftedSize node) :
    (memory.read 576 32).1 = oldCount.toBytes := by
  rw [Mem.Reads.read h.reads, h.oldCount_read]

theorem RootMemoryCarrier.read_shiftedSize
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : RootMemoryCarrier memory oldCount shiftedSize node) :
    (memory.read 608 32).1 = shiftedSize.toBytes := by
  rw [Mem.Reads.read h.reads, h.shiftedSize_read]

theorem RootMemoryCarrier.read_node
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : RootMemoryCarrier memory oldCount shiftedSize node) :
    (memory.read 640 32).1 = node.toBytes := by
  rw [Mem.Reads.read h.reads, h.node_read]

/-- Staging a word at byte zero leaves the current-node register readable. -/
theorem RootMemoryCarrier.read_node_after_write_zero
    {memory : Mem} {oldCount shiftedSize node value : B256}
    (h : RootMemoryCarrier memory oldCount shiftedSize node) :
    Bytes.toB256 ((memory.write 0 value.toBytes).read 640 32).1 =
      node := by
  have hwrites :
      Mem.Reads (memory.write 0 value.toBytes)
        (Bytes.writeAt h.image 0 value.toBytes) :=
    Mem.Reads.write h.wf h.reads _ _
  rw [Mem.Reads.read hwrites,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega),
    h.node_read, B256.toB256_toBytes]

/-- Shift the fold-size register right by one word-bit. -/
def RootMemoryCarrier.shiftSize
    {memory : Mem} {oldCount shiftedSize node : B256}
    (h : RootMemoryCarrier memory oldCount shiftedSize node) :
    RootMemoryCarrier
      (memory.write 608 (shiftedSize >>> 1).toBytes)
      oldCount (shiftedSize >>> 1) node := by
  let next := shiftedSize >>> 1
  let M := memory.write 608 next.toBytes
  let I := Bytes.writeAt h.image 608 next.toBytes
  have hwf : Mem.Wf M := Mem.Wf.write h.wf _ _
  have hreads : Mem.Reads M I := Mem.Reads.write h.wf h.reads _ _
  have hsize : M.size = 672 := by
    dsimp only [M]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]
      omega), h.size_eq]
  have hlen : I.length = 672 := by
    dsimp only [I]
    rw [Bytes.length_writeAt, h.image_length, B256.length_toBytes]
    omega
  have hold : I.sliceD 576 32 0 = oldCount.toBytes := by
    dsimp only [I]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.oldCount_read
  have hshift : I.sliceD 608 32 0 = next.toBytes := by
    dsimp only [I]
    rw [show 32 = next.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  have hnode : I.sliceD 640 32 0 = node.toBytes := by
    dsimp only [I]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    exact h.node_read
  change RootMemoryCarrier M oldCount next node
  exact ⟨I, hwf, hreads, hsize, hlen, hold, hshift, hnode⟩

/-- Overwrite the first two words with the next SHA-256 pair. -/
def RootMemoryCarrier.stagePair
    {memory : Mem} {oldCount shiftedSize node left right : B256}
    (h : RootMemoryCarrier memory oldCount shiftedSize node) :
    RootPairMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 right.toBytes)
      oldCount shiftedSize left right := by
  let M1 := memory.write 0 left.toBytes
  let I1 := Bytes.writeAt h.image 0 left.toBytes
  let M2 := M1.write 32 right.toBytes
  let I2 := Bytes.writeAt I1 32 right.toBytes
  have hwf1 : Mem.Wf M1 := Mem.Wf.write h.wf _ _
  have hreads1 : Mem.Reads M1 I1 := Mem.Reads.write h.wf h.reads _ _
  have hwf2 : Mem.Wf M2 := Mem.Wf.write hwf1 _ _
  have hreads2 : Mem.Reads M2 I2 := Mem.Reads.write hwf1 hreads1 _ _
  have hsize1 : M1.size = 672 := by
    dsimp only [M1]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]
      omega), h.size_eq]
  have hsize2 : M2.size = 672 := by
    dsimp only [M2]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hsize1]
      omega), hsize1]
  have hlen1 : I1.length = 672 := by
    dsimp only [I1]
    rw [Bytes.length_writeAt, h.image_length, B256.length_toBytes]
    omega
  have hlen2 : I2.length = 672 := by
    dsimp only [I2]
    rw [Bytes.length_writeAt, hlen1, B256.length_toBytes]
    omega
  have hold : I2.sliceD 576 32 0 = oldCount.toBytes := by
    dsimp only [I2]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    dsimp only [I1]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    exact h.oldCount_read
  have hshift : I2.sliceD 608 32 0 = shiftedSize.toBytes := by
    dsimp only [I2]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    dsimp only [I1]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    exact h.shiftedSize_read
  have hpairImage :
      I2.sliceD 0 64 0 = left.toBytes ++ right.toBytes := by
    exact Bytes.sliceD_stagedPair h.image left right
  have hsha := Mem.Reads.read hreads2 0 64
  change M2.data.sliceD 0 64 0 = I2.sliceD 0 64 0 at hsha
  rw [hpairImage] at hsha
  exact ⟨I2, hwf2, hreads2, hsize2, hlen2,
    hold, hshift, hsha⟩

/-- Write the staged pair's digest back into the current-node register. -/
def RootPairMemoryCarrier.finishHash
    {memory : Mem} {oldCount shiftedSize left right : B256}
    (h : RootPairMemoryCarrier memory oldCount shiftedSize left right) :
    RootMemoryCarrier
      (memory.write 640
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes)
      oldCount shiftedSize
      (Bytes.sha256 (left.toBytes ++ right.toBytes)) := by
  let digest := Bytes.sha256 (left.toBytes ++ right.toBytes)
  let M := memory.write 640 digest.toBytes
  let I := Bytes.writeAt h.image 640 digest.toBytes
  have hwf : Mem.Wf M := Mem.Wf.write h.wf _ _
  have hreads : Mem.Reads M I := Mem.Reads.write h.wf h.reads _ _
  have hsize : M.size = 672 := by
    dsimp only [M]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]), h.size_eq]
  have hlen : I.length = 672 := by
    dsimp only [I]
    rw [Bytes.length_writeAt, h.image_length, B256.length_toBytes]
    omega
  have hold : I.sliceD 576 32 0 = oldCount.toBytes := by
    dsimp only [I]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.oldCount_read
  have hshift : I.sliceD 608 32 0 = shiftedSize.toBytes := by
    dsimp only [I]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.shiftedSize_read
  have hnode : I.sliceD 640 32 0 = digest.toBytes := by
    dsimp only [I]
    rw [show 32 = digest.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  change RootMemoryCarrier M oldCount shiftedSize digest
  exact ⟨I, hwf, hreads, hsize, hlen, hold, hshift, hnode⟩

end Blanc.BeaconDeposit
