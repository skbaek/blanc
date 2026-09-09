import Blanc.BeaconDeposit
import Blanc.BeaconDepositEncoding
import Blanc.MemoryLayout

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

/-- The decoder's exact word writes in execution order: length then offset for
each dynamic tail. -/
def depositDecodedWrites (data : Bytes) : List (Nat × B256) :=
  [(96, depositLengthWord data 0),
    (0, depositOffsetWord data 0),
    (128, depositLengthWord data 1),
    (32, depositOffsetWord data 1),
    (160, depositLengthWord data 2),
    (64, depositOffsetWord data 2)]

/-- Exact memory after all three successful dynamic-tail decoders. -/
def depositDecodedMemory (data : Bytes) : Mem :=
  (MemoryStage.words (depositDecodedWrites data)).applyMemory Mem.empty

/-- Symbolic byte image corresponding to `depositDecodedMemory`. -/
def depositDecodedImage (data : Bytes) : Bytes :=
  (MemoryStage.words (depositDecodedWrites data)).applyImage []

/-- The six decoder temporaries, with both a symbolic image and direct read
coordinates for downstream event staging. -/
structure DepositDecodedMemoryCarrier
    (memory : Mem) (data : Bytes) : Type where
  image : Bytes
  image_eq : image = depositDecodedImage data
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
  have hinv := MemoryStage.wf_reads
    (MemoryStage.words (depositDecodedWrites data))
    Mem.wf_empty Mem.reads_empty
  refine ⟨depositDecodedImage data, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [depositDecodedMemory] using hinv.1
  · simpa only [depositDecodedMemory, depositDecodedImage] using hinv.2
  · rw [depositDecodedMemory,
      MemoryStage.applyMemory_words_size _ _ (by decide +kernel)]
    simp only [depositDecodedWrites, List.map_cons, List.map_nil,
      memExtsSize, memExtSize]
    change 32 * max 0 6 = 192
    decide +kernel
  · rw [depositDecodedImage, MemoryStage.applyImage_words_length]
    simp [depositDecodedWrites]
  · simpa only [depositDecodedImage, depositDecodedWrites,
      List.cons_append, List.nil_append] using
      (MemoryStage.read_written_word
        [(96, depositLengthWord data 0)]
        [(128, depositLengthWord data 1),
          (32, depositOffsetWord data 1),
          (160, depositLengthWord data 2),
          (64, depositOffsetWord data 2)]
        [] 0 (depositOffsetWord data 0) (by
          simp [MemoryStage.words, MemoryStage.avoids]))
  · simpa only [depositDecodedImage, depositDecodedWrites,
      List.cons_append, List.nil_append] using
      (MemoryStage.read_written_word
        [(96, depositLengthWord data 0),
          (0, depositOffsetWord data 0),
          (128, depositLengthWord data 1)]
        [(160, depositLengthWord data 2),
          (64, depositOffsetWord data 2)]
        [] 32 (depositOffsetWord data 1) (by
          simp [MemoryStage.words, MemoryStage.avoids,
            B256.length_toBytes]))
  · simpa only [depositDecodedImage, depositDecodedWrites,
      List.cons_append, List.nil_append] using
      (MemoryStage.read_written_word
        [(96, depositLengthWord data 0),
          (0, depositOffsetWord data 0),
          (128, depositLengthWord data 1),
          (32, depositOffsetWord data 1),
          (160, depositLengthWord data 2)]
        [] [] 64 (depositOffsetWord data 2) (by
          simp [MemoryStage.words, MemoryStage.avoids]))
  · simpa only [depositDecodedImage, depositDecodedWrites,
      List.cons_append, List.nil_append] using
      (MemoryStage.read_written_word
        []
        [(0, depositOffsetWord data 0),
          (128, depositLengthWord data 1),
          (32, depositOffsetWord data 1),
          (160, depositLengthWord data 2),
          (64, depositOffsetWord data 2)]
        [] 96 (depositLengthWord data 0) (by
          simp [MemoryStage.words, MemoryStage.avoids,
            B256.length_toBytes]))
  · simpa only [depositDecodedImage, depositDecodedWrites,
      List.cons_append, List.nil_append] using
      (MemoryStage.read_written_word
        [(96, depositLengthWord data 0),
          (0, depositOffsetWord data 0)]
        [(32, depositOffsetWord data 1),
          (160, depositLengthWord data 2),
          (64, depositOffsetWord data 2)]
        [] 128 (depositLengthWord data 1) (by
          simp [MemoryStage.words, MemoryStage.avoids,
            B256.length_toBytes]))
  · simpa only [depositDecodedImage, depositDecodedWrites,
      List.cons_append, List.nil_append] using
      (MemoryStage.read_written_word
        [(96, depositLengthWord data 0),
          (0, depositOffsetWord data 0),
          (128, depositLengthWord data 1),
          (32, depositOffsetWord data 1)]
        [(64, depositOffsetWord data 2)]
        [] 160 (depositLengthWord data 2) (by
          simp [MemoryStage.words, MemoryStage.avoids,
            B256.length_toBytes]))

end Blanc.BeaconDeposit
