import Blanc.BeaconDeposit
import Blanc.BeaconDepositEncoding

/-!
# Beacon deposit ABI-decoder memory

The executable decoder retains the three dynamic offsets in words `0..2` and
their lengths in words `3..5`.  This module connects the independent calldata
reader used by `DepositAbiDecodable` to the EVM reader, then packages the exact
six-word memory image established on the successful decoder path.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- Reading calldata through a machine word made from an in-range natural
offset is exactly the independent reader used by the ABI specification. -/
theorem dataWord_toB256
    {sevm : Sevm} {offset : Nat} (hbound : offset < 2 ^ 256) :
    Sevm.dataWord sevm (Nat.toB256 offset) =
      calldataWord sevm.data offset := by
  unfold Sevm.dataWord calldataWord
  rw [B256.toNat_toB256_of_lt hbound]

/-- The machine word retained for one dynamic argument's offset. -/
def depositOffsetWord (data : Bytes) (head : Nat) : B256 :=
  Nat.toB256 (dynamicOffset data head)

/-- The machine word retained for one dynamic argument's length. -/
def depositLengthWord (data : Bytes) (head : Nat) : B256 :=
  Nat.toB256 (dynamicLength data head)

@[simp] theorem depositOffsetWord_eq_calldataWord
    (data : Bytes) (head : Nat) :
    depositOffsetWord data head =
      calldataWord data (4 + 32 * head) := by
  unfold depositOffsetWord dynamicOffset
  exact Jaune.toB256_toNat _

@[simp] theorem depositLengthWord_eq_calldataWord
    (data : Bytes) (head : Nat) :
    depositLengthWord data head =
      calldataWord data (4 + dynamicOffset data head) := by
  unfold depositLengthWord dynamicLength
  exact Jaune.toB256_toNat _

theorem dataWord_depositOffsetWord
    {sevm : Sevm} (head : Nat)
    (hbound : 4 + 32 * head < 2 ^ 256) :
    Sevm.dataWord sevm (Nat.toB256 (4 + 32 * head)) =
      depositOffsetWord sevm.data head := by
  rw [dataWord_toB256 hbound, depositOffsetWord_eq_calldataWord]

theorem dataWord_depositLengthWord
    {sevm : Sevm} (head : Nat)
    (hbound : 4 + dynamicOffset sevm.data head < 2 ^ 256) :
    Sevm.dataWord sevm
        (Nat.toB256 (4 + dynamicOffset sevm.data head)) =
      depositLengthWord sevm.data head := by
  rw [dataWord_toB256 hbound, depositLengthWord_eq_calldataWord]

theorem depositOffsetWord_toNat
    {data : Bytes} {head : Nat}
    (hbound : dynamicOffset data head < 2 ^ 256) :
    (depositOffsetWord data head).toNat = dynamicOffset data head := by
  unfold depositOffsetWord
  exact B256.toNat_toB256_of_lt hbound

theorem depositLengthWord_toNat
    {data : Bytes} {head : Nat}
    (hbound : dynamicLength data head < 2 ^ 256) :
    (depositLengthWord data head).toNat = dynamicLength data head := by
  unfold depositLengthWord
  exact B256.toNat_toB256_of_lt hbound

theorem depositOffsetWord_add_four
    {data : Bytes} {head : Nat}
    (hbound : dynamicOffset data head < 2 ^ 32) :
    depositOffsetWord data head + 4 =
      Nat.toB256 (4 + dynamicOffset data head) := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [depositOffsetWord_toNat (by omega),
      B256.toNat_toB256_of_lt (by omega)]
    rw [show (4 : B256).toNat = 4 by decide +kernel]
    omega
  · unfold B256.Nof
    rw [depositOffsetWord_toNat (by omega)]
    change dynamicOffset data head + 4 < 2 ^ 256
    omega

/-- Exact memory after all three successful dynamic-tail decoders.  The write
order is the program's order: length, then offset, for each tail. -/
def depositDecodedMemory (data : Bytes) : Mem :=
  (((((Mem.empty.write 96 (depositLengthWord data 0).toBytes)
      |>.write 0 (depositOffsetWord data 0).toBytes)
    |>.write 128 (depositLengthWord data 1).toBytes)
    |>.write 32 (depositOffsetWord data 1).toBytes)
    |>.write 160 (depositLengthWord data 2).toBytes)
    |>.write 64 (depositOffsetWord data 2).toBytes

/-- Symbolic byte image corresponding to `depositDecodedMemory`. -/
def depositDecodedImage (data : Bytes) : Bytes :=
  (((((Bytes.writeAt [] 96 (depositLengthWord data 0).toBytes)
      |> fun image => Bytes.writeAt image 0
        (depositOffsetWord data 0).toBytes)
    |> fun image => Bytes.writeAt image 128
      (depositLengthWord data 1).toBytes)
    |> fun image => Bytes.writeAt image 32
      (depositOffsetWord data 1).toBytes)
    |> fun image => Bytes.writeAt image 160
      (depositLengthWord data 2).toBytes)
    |> fun image => Bytes.writeAt image 64
      (depositOffsetWord data 2).toBytes

/-- The six decoder temporaries, with both a symbolic image and direct read
coordinates for downstream event staging. -/
structure DepositDecodedMemoryCarrier
    (memory : Mem) (data : Bytes) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 192
  image_length : image.length = 192
  offset0_read : image.sliceD 0 32 0 = (depositOffsetWord data 0).toBytes
  offset1_read : image.sliceD 32 32 0 = (depositOffsetWord data 1).toBytes
  offset2_read : image.sliceD 64 32 0 = (depositOffsetWord data 2).toBytes
  length0_read : image.sliceD 96 32 0 = (depositLengthWord data 0).toBytes
  length1_read : image.sliceD 128 32 0 = (depositLengthWord data 1).toBytes
  length2_read : image.sliceD 160 32 0 = (depositLengthWord data 2).toBytes

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

theorem DepositDecodedMemoryCarrier.read_offset0
    {memory : Mem} {data : Bytes}
    (h : DepositDecodedMemoryCarrier memory data) :
    (memory.read 0 32).1 = (depositOffsetWord data 0).toBytes := by
  rw [Mem.Reads.read h.reads, h.offset0_read]

theorem DepositDecodedMemoryCarrier.read_offset1
    {memory : Mem} {data : Bytes}
    (h : DepositDecodedMemoryCarrier memory data) :
    (memory.read 32 32).1 = (depositOffsetWord data 1).toBytes := by
  rw [Mem.Reads.read h.reads, h.offset1_read]

theorem DepositDecodedMemoryCarrier.read_offset2
    {memory : Mem} {data : Bytes}
    (h : DepositDecodedMemoryCarrier memory data) :
    (memory.read 64 32).1 = (depositOffsetWord data 2).toBytes := by
  rw [Mem.Reads.read h.reads, h.offset2_read]

theorem DepositDecodedMemoryCarrier.read_length0
    {memory : Mem} {data : Bytes}
    (h : DepositDecodedMemoryCarrier memory data) :
    (memory.read 96 32).1 = (depositLengthWord data 0).toBytes := by
  rw [Mem.Reads.read h.reads, h.length0_read]

theorem DepositDecodedMemoryCarrier.read_length1
    {memory : Mem} {data : Bytes}
    (h : DepositDecodedMemoryCarrier memory data) :
    (memory.read 128 32).1 = (depositLengthWord data 1).toBytes := by
  rw [Mem.Reads.read h.reads, h.length1_read]

theorem DepositDecodedMemoryCarrier.read_length2
    {memory : Mem} {data : Bytes}
    (h : DepositDecodedMemoryCarrier memory data) :
    (memory.read 160 32).1 = (depositLengthWord data 2).toBytes := by
  rw [Mem.Reads.read h.reads, h.length2_read]

/-- The concrete decoder image satisfies the reusable six-word carrier. -/
def depositDecodedMemory_carrier (data : Bytes) :
    DepositDecodedMemoryCarrier (depositDecodedMemory data) data := by
  let M0 := Mem.empty
  let I0 : Bytes := []
  let M1 := M0.write 96 (depositLengthWord data 0).toBytes
  let I1 := Bytes.writeAt I0 96 (depositLengthWord data 0).toBytes
  let M2 := M1.write 0 (depositOffsetWord data 0).toBytes
  let I2 := Bytes.writeAt I1 0 (depositOffsetWord data 0).toBytes
  let M3 := M2.write 128 (depositLengthWord data 1).toBytes
  let I3 := Bytes.writeAt I2 128 (depositLengthWord data 1).toBytes
  let M4 := M3.write 32 (depositOffsetWord data 1).toBytes
  let I4 := Bytes.writeAt I3 32 (depositOffsetWord data 1).toBytes
  let M5 := M4.write 160 (depositLengthWord data 2).toBytes
  let I5 := Bytes.writeAt I4 160 (depositLengthWord data 2).toBytes
  let M6 := M5.write 64 (depositOffsetWord data 2).toBytes
  let I6 := Bytes.writeAt I5 64 (depositOffsetWord data 2).toBytes
  have hwf0 : Mem.Wf M0 := Mem.wf_empty
  have hreads0 : Mem.Reads M0 I0 := Mem.reads_empty
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  have hreads1 : Mem.Reads M1 I1 := Mem.Reads.write hwf0 hreads0 _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hreads2 : Mem.Reads M2 I2 := Mem.Reads.write hwf1 hreads1 _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hreads3 : Mem.Reads M3 I3 := Mem.Reads.write hwf2 hreads2 _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hreads4 : Mem.Reads M4 I4 := Mem.Reads.write hwf3 hreads3 _ _
  have hwf5 : Mem.Wf M5 := hwf4.write _ _
  have hreads5 : Mem.Reads M5 I5 := Mem.Reads.write hwf4 hreads4 _ _
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hreads6 : Mem.Reads M6 I6 := Mem.Reads.write hwf5 hreads5 _ _
  have hsize1 : M1.size = 128 := by
    dsimp only [M1, M0]
    rw [Mem.size_write_word_at]
    decide +kernel
  have hsize2 : M2.size = 128 := by
    dsimp only [M2]
    rw [Mem.size_write_word_at, hsize1]
    decide +kernel
  have hsize3 : M3.size = 160 := by
    dsimp only [M3]
    rw [Mem.size_write_word_at, hsize2]
    decide +kernel
  have hsize4 : M4.size = 160 := by
    dsimp only [M4]
    rw [Mem.size_write_word_at, hsize3]
    decide +kernel
  have hsize5 : M5.size = 192 := by
    dsimp only [M5]
    rw [Mem.size_write_word_at, hsize4]
    decide +kernel
  have hsize6 : M6.size = 192 := by
    dsimp only [M6]
    rw [Mem.size_write_word_at, hsize5]
    decide +kernel
  have hlen1 : I1.length = 128 := by
    dsimp only [I1, I0]
    rw [Bytes.length_writeAt, B256.length_toBytes]
    decide +kernel
  have hlen2 : I2.length = 128 := by
    dsimp only [I2]
    rw [Bytes.length_writeAt, hlen1, B256.length_toBytes]
    decide +kernel
  have hlen3 : I3.length = 160 := by
    dsimp only [I3]
    rw [Bytes.length_writeAt, hlen2, B256.length_toBytes]
    decide +kernel
  have hlen4 : I4.length = 160 := by
    dsimp only [I4]
    rw [Bytes.length_writeAt, hlen3, B256.length_toBytes]
    decide +kernel
  have hlen5 : I5.length = 192 := by
    dsimp only [I5]
    rw [Bytes.length_writeAt, hlen4, B256.length_toBytes]
    decide +kernel
  have hlen6 : I6.length = 192 := by
    dsimp only [I6]
    rw [Bytes.length_writeAt, hlen5, B256.length_toBytes]
    decide +kernel
  have hoffset0 :
      I6.sliceD 0 32 0 = (depositOffsetWord data 0).toBytes := by
    dsimp only [I6]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I3]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I2]
    rw [show 32 = (depositOffsetWord data 0).toBytes.length by
      rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  have hoffset1 :
      I6.sliceD 32 32 0 = (depositOffsetWord data 1).toBytes := by
    dsimp only [I6]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I4]
    rw [show 32 = (depositOffsetWord data 1).toBytes.length by
      rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  have hoffset2 :
      I6.sliceD 64 32 0 = (depositOffsetWord data 2).toBytes := by
    dsimp only [I6]
    rw [show 32 = (depositOffsetWord data 2).toBytes.length by
      rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  have hlength0 :
      I6.sliceD 96 32 0 = (depositLengthWord data 0).toBytes := by
    dsimp only [I6]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    dsimp only [I5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I4]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; omega)]
    dsimp only [I3]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I2]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; omega)]
    dsimp only [I1]
    rw [show 32 = (depositLengthWord data 0).toBytes.length by
      rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  have hlength1 :
      I6.sliceD 128 32 0 = (depositLengthWord data 1).toBytes := by
    dsimp only [I6]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; omega)]
    dsimp only [I5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    dsimp only [I4]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; omega)]
    dsimp only [I3]
    rw [show 32 = (depositLengthWord data 1).toBytes.length by
      rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  have hlength2 :
      I6.sliceD 160 32 0 = (depositLengthWord data 2).toBytes := by
    dsimp only [I6]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; omega)]
    dsimp only [I5]
    rw [show 32 = (depositLengthWord data 2).toBytes.length by
      rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  change DepositDecodedMemoryCarrier M6 data
  exact ⟨I6, hwf6, hreads6, hsize6, hlen6,
    hoffset0, hoffset1, hoffset2, hlength0, hlength1, hlength2⟩

end Blanc.BeaconDeposit
