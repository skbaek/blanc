import Blanc.BeaconDepositEventMemory
import Blanc.BeaconDepositSha

/-!
# Beacon deposit reconstruction memory carriers

The event stage leaves five SHA-256 source regions and two persistent machine
words in memory.  Reconstruction overwrites only words `0`, `1`, `20`, `22`,
and `23`, so these source facts remain stable while the three digest registers
grow from the initial 704-byte image to 768 bytes.
-/

namespace Blanc.BeaconDeposit

open Jaune

private lemma Bytes.sliceD_writeAt_after_reconstruct
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

private lemma Bytes.sliceD_stagedPair_reconstruct
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

/-- The source windows retained throughout deposit-data reconstruction.

The byte-valued fields deliberately record the machine image before any
fixed-width decoding.  Later bridge lemmas use the successful ABI length
guards to identify their 32-byte `Bytes.toB256` round trips with the model's
withdrawal, signature-tail, and padded-amount inputs.
-/
structure ReconstructSourceMemoryCarrier
    (memory : Mem)
    (pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes)
    (oldCount amount : B256) (size : Nat) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = size
  pubkeyInput_read : image.sliceD 192 64 0 = pubkeyInput
  withdrawal_read : image.sliceD 288 32 0 = withdrawal
  amountPadded_read : image.sliceD 352 32 0 = amountPadded
  signatureFirst_read : image.sliceD 416 64 0 = signatureFirst
  signatureTail_read : image.sliceD 480 32 0 = signatureTail
  oldCount_read : image.sliceD 576 32 0 = oldCount.toBytes
  amount_read : image.sliceD 672 32 0 = amount.toBytes

theorem ReconstructSourceMemoryCarrier.shaPubkeyInput
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    memory.data.sliceD 192 64 0 = pubkeyInput := by
  change (memory.read 192 64).1 = pubkeyInput
  rw [Mem.Reads.read h.reads, h.pubkeyInput_read]

theorem ReconstructSourceMemoryCarrier.shaSignatureFirstInput
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    memory.data.sliceD 416 64 0 = signatureFirst := by
  change (memory.read 416 64).1 = signatureFirst
  rw [Mem.Reads.read h.reads, h.signatureFirst_read]

theorem ReconstructSourceMemoryCarrier.readWithdrawal
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    Bytes.toB256 (memory.read 288 32).1 = Bytes.toB256 withdrawal := by
  rw [Mem.Reads.read h.reads, h.withdrawal_read]

theorem ReconstructSourceMemoryCarrier.readAmountPadded
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    Bytes.toB256 (memory.read 352 32).1 = Bytes.toB256 amountPadded := by
  rw [Mem.Reads.read h.reads, h.amountPadded_read]

theorem ReconstructSourceMemoryCarrier.readSignatureTail
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    Bytes.toB256 (memory.read 480 32).1 = Bytes.toB256 signatureTail := by
  rw [Mem.Reads.read h.reads, h.signatureTail_read]

theorem ReconstructSourceMemoryCarrier.readOldCount
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    Bytes.toB256 (memory.read 576 32).1 = oldCount := by
  rw [Mem.Reads.read h.reads, h.oldCount_read, B256.toB256_toBytes]

theorem ReconstructSourceMemoryCarrier.readAmount
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size) :
    Bytes.toB256 (memory.read 672 32).1 = amount := by
  rw [Mem.Reads.read h.reads, h.amount_read, B256.toB256_toBytes]

/-- The two memory windows touched by one contract `sha64` call. -/
def reconstructionShaWindows (inputWord outputWord : B256) :
    List (Nat × Nat) :=
  [⟨(inputWord * 32).toNat, 64⟩,
    ⟨(outputWord * 32).toNat, 32⟩]

/-- Logical memory expansion changes no retained source byte. -/
def ReconstructSourceMemoryCarrier.extendForHash
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size)
    (inputWord outputWord : B256) :
    ReconstructSourceMemoryCarrier
      (memory.extends (reconstructionShaWindows inputWord outputWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount
      (memExtsSize size (reconstructionShaWindows inputWord outputWord)) := by
  refine ⟨h.image, Mem.Wf.extends _ h.wf, Mem.Reads.extends _ h.reads,
    ?_, h.pubkeyInput_read, h.withdrawal_read, h.amountPadded_read,
    h.signatureFirst_read, h.signatureTail_read,
    h.oldCount_read, h.amount_read⟩
  change memExtsSize memory.size (reconstructionShaWindows inputWord outputWord) =
    memExtsSize size (reconstructionShaWindows inputWord outputWord)
  rw [h.size_eq]

/-- A staging write below byte 192 preserves every reconstruction source. -/
def ReconstructSourceMemoryCarrier.writeBeforeSources
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size)
    (n : Nat) (xs : Bytes)
    (hbefore : n + xs.length ≤ 192)
    (hfit : n + xs.length ≤ size) :
    ReconstructSourceMemoryCarrier (memory.write n xs)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount size := by
  let image' := Bytes.writeAt h.image n xs
  refine ⟨image', h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by rw [h.size_eq]; exact hfit), h.size_eq]
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ hbefore]
    exact h.pubkeyInput_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by omega)]
    exact h.withdrawal_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by omega)]
    exact h.amountPadded_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by omega)]
    exact h.signatureFirst_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by omega)]
    exact h.signatureTail_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by omega)]
    exact h.oldCount_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by omega)]
    exact h.amount_read

/-- A digest write beginning at or above byte 704 preserves every source. -/
def ReconstructSourceMemoryCarrier.writeAfterSources
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size)
    (n : Nat) (xs : Bytes)
    (hstart : 704 ≤ n)
    (hfit : n + xs.length ≤ size) :
    ReconstructSourceMemoryCarrier (memory.write n xs)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount size := by
  let image' := Bytes.writeAt h.image n xs
  refine ⟨image', h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by rw [h.size_eq]; exact hfit), h.size_eq]
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.pubkeyInput_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.withdrawal_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.amountPadded_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.signatureFirst_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.signatureTail_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.oldCount_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.amount_read

/-- Writing the node register at byte 640 preserves all reconstruction inputs. -/
def ReconstructSourceMemoryCarrier.writeNodeSource
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size)
    (node : B256) (hfit : 672 ≤ size) :
    ReconstructSourceMemoryCarrier (memory.write 640 node.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount size := by
  let image' := Bytes.writeAt h.image 640 node.toBytes
  refine ⟨image', h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h.size_eq]
      exact hfit), h.size_eq]
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.pubkeyInput_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.withdrawal_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.amountPadded_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.signatureFirst_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.signatureTail_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.oldCount_read
  · dsimp only [image']
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    exact h.amount_read

/-- Reconstruction sources plus the digest currently held in word 20. -/
structure ReconstructNodeMemoryCarrier
    (memory : Mem)
    (pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes)
    (oldCount amount node : B256) (size : Nat) : Type where
  source : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
    signatureTail withdrawal amountPadded oldCount amount size
  node_read : source.image.sliceD 640 32 0 = node.toBytes

/-- A source carrier becomes a node carrier after the SHA output write. -/
def ReconstructSourceMemoryCarrier.writeNode
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {size : Nat}
    (h : ReconstructSourceMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount size)
    (node : B256) (hfit : 672 ≤ size) :
    ReconstructNodeMemoryCarrier (memory.write 640 node.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node size := by
  let source' := h.writeNodeSource node hfit
  refine ⟨source', ?_⟩
  change (Bytes.writeAt h.image 640 node.toBytes).sliceD 640 32 0 =
    node.toBytes
  rw [show 32 = node.toBytes.length by rw [B256.length_toBytes]]
  exact Bytes.sliceD_writeAt _ _ _

theorem ReconstructNodeMemoryCarrier.readNode
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node : B256} {size : Nat}
    (h : ReconstructNodeMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node size) :
    Bytes.toB256 (memory.read 640 32).1 = node := by
  rw [Mem.Reads.read h.source.reads, h.node_read, B256.toB256_toBytes]

/-- Logical SHA expansion preserves the established node register. -/
def ReconstructNodeMemoryCarrier.extendForHash
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node : B256} {size : Nat}
    (h : ReconstructNodeMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node size)
    (inputWord outputWord : B256) :
    ReconstructNodeMemoryCarrier
      (memory.extends (reconstructionShaWindows inputWord outputWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node
      (memExtsSize size (reconstructionShaWindows inputWord outputWord)) := by
  exact ⟨h.source.extendForHash inputWord outputWord, h.node_read⟩

/-- Reconstruction sources and node plus the digest held in word 22. -/
structure ReconstructIntermediateMemoryCarrier
    (memory : Mem)
    (pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes)
    (oldCount amount node intermediate : B256) (size : Nat) : Type where
  node : ReconstructNodeMemoryCarrier memory pubkeyInput signatureFirst
    signatureTail withdrawal amountPadded oldCount amount node size
  intermediate_read : node.source.image.sliceD 704 32 0 =
    intermediate.toBytes

/-- Writing word 22 after the SHA call creates the intermediate carrier. -/
def ReconstructNodeMemoryCarrier.writeIntermediate
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node : B256} {size : Nat}
    (h : ReconstructNodeMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node size)
    (intermediate : B256) (hfit : 736 ≤ size) :
    ReconstructIntermediateMemoryCarrier
      (memory.write 704 intermediate.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate size := by
  let source' := h.source.writeAfterSources 704 intermediate.toBytes
    (by omega) (by rw [B256.length_toBytes]; exact hfit)
  have hnode : source'.image.sliceD 640 32 0 = node.toBytes := by
    change (Bytes.writeAt h.source.image 704 intermediate.toBytes).sliceD
      640 32 0 = node.toBytes
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.node_read
  let node' : ReconstructNodeMemoryCarrier
      (memory.write 704 intermediate.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node size := ⟨source', hnode⟩
  refine ⟨node', ?_⟩
  change (Bytes.writeAt h.source.image 704 intermediate.toBytes).sliceD
    704 32 0 = intermediate.toBytes
  rw [show 32 = intermediate.toBytes.length by rw [B256.length_toBytes]]
  exact Bytes.sliceD_writeAt _ _ _

theorem ReconstructIntermediateMemoryCarrier.readIntermediate
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate : B256} {size : Nat}
    (h : ReconstructIntermediateMemoryCarrier memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount
      node intermediate size) :
    Bytes.toB256 (memory.read 704 32).1 = intermediate := by
  rw [Mem.Reads.read h.node.source.reads, h.intermediate_read,
    B256.toB256_toBytes]

/-- Logical SHA expansion preserves both established digest registers. -/
def ReconstructIntermediateMemoryCarrier.extendForHash
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate : B256} {size : Nat}
    (h : ReconstructIntermediateMemoryCarrier memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount
      node intermediate size)
    (inputWord outputWord : B256) :
    ReconstructIntermediateMemoryCarrier
      (memory.extends (reconstructionShaWindows inputWord outputWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate
      (memExtsSize size (reconstructionShaWindows inputWord outputWord)) := by
  exact ⟨h.node.extendForHash inputWord outputWord, h.intermediate_read⟩

/-- The node/intermediate carrier after staging a 64-byte pair in words 0–1. -/
structure ReconstructIntermediatePairMemoryCarrier
    (memory : Mem)
    (pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes)
    (oldCount amount node intermediate left right : B256)
    (size : Nat) : Type where
  intermediate : ReconstructIntermediateMemoryCarrier memory pubkeyInput
    signatureFirst signatureTail withdrawal amountPadded oldCount amount
    node intermediate size
  shaInput : memory.data.sliceD 0 64 0 = left.toBytes ++ right.toBytes

/-- Stage two digest words without losing either established register. -/
def ReconstructIntermediateMemoryCarrier.stagePair
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate : B256} {size : Nat}
    (h : ReconstructIntermediateMemoryCarrier memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount
      node intermediate size)
    (left right : B256) (hfit : 64 ≤ size) :
    ReconstructIntermediatePairMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 right.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate left right size := by
  let source1 := h.node.source.writeBeforeSources 0 left.toBytes
    (by rw [B256.length_toBytes]; omega)
    (by rw [B256.length_toBytes]; omega)
  let source2 := source1.writeBeforeSources 32 right.toBytes
    (by rw [B256.length_toBytes]; omega)
    (by rw [B256.length_toBytes]; omega)
  have hnode : source2.image.sliceD 640 32 0 = node.toBytes := by
    change (Bytes.writeAt
      (Bytes.writeAt h.node.source.image 0 left.toBytes)
      32 right.toBytes).sliceD 640 32 0 = node.toBytes
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega),
      Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
        rw [B256.length_toBytes]
        omega)]
    exact h.node.node_read
  let node' : ReconstructNodeMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 right.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node size := ⟨source2, hnode⟩
  have hintermediate : node'.source.image.sliceD 704 32 0 =
      intermediate.toBytes := by
    change (Bytes.writeAt
      (Bytes.writeAt h.node.source.image 0 left.toBytes)
      32 right.toBytes).sliceD 704 32 0 = intermediate.toBytes
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega),
      Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
        rw [B256.length_toBytes]
        omega)]
    exact h.intermediate_read
  let intermediate' : ReconstructIntermediateMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 right.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate size :=
    ⟨node', hintermediate⟩
  have hpairImage : intermediate'.node.source.image.sliceD 0 64 0 =
      left.toBytes ++ right.toBytes := by
    change (Bytes.writeAt
      (Bytes.writeAt h.node.source.image 0 left.toBytes)
      32 right.toBytes).sliceD 0 64 0 = left.toBytes ++ right.toBytes
    exact Bytes.sliceD_stagedPair_reconstruct _ _ _
  have hsha := Mem.Reads.read intermediate'.node.source.reads 0 64
  change ((memory.write 0 left.toBytes).write 32 right.toBytes).data.sliceD
    0 64 0 = intermediate'.node.source.image.sliceD 0 64 0 at hsha
  rw [hpairImage] at hsha
  exact ⟨intermediate', hsha⟩

/-- All three reconstruction digest registers after the third SHA output. -/
structure ReconstructRegistersMemoryCarrier
    (memory : Mem)
    (pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes)
    (oldCount amount node intermediate second : B256)
    (size : Nat) : Type where
  intermediate : ReconstructIntermediateMemoryCarrier memory pubkeyInput
    signatureFirst signatureTail withdrawal amountPadded oldCount amount
    node intermediate size
  second_read : intermediate.node.source.image.sliceD 736 32 0 =
    second.toBytes

/-- Writing word 23 completes the three-register reconstruction carrier. -/
def ReconstructIntermediateMemoryCarrier.writeSecond
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate : B256} {size : Nat}
    (h : ReconstructIntermediateMemoryCarrier memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount
      node intermediate size)
    (second : B256) (hfit : 768 ≤ size) :
    ReconstructRegistersMemoryCarrier (memory.write 736 second.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second size := by
  let source' := h.node.source.writeAfterSources 736 second.toBytes
    (by omega) (by rw [B256.length_toBytes]; exact hfit)
  have hnode : source'.image.sliceD 640 32 0 = node.toBytes := by
    change (Bytes.writeAt h.node.source.image 736 second.toBytes).sliceD
      640 32 0 = node.toBytes
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.node.node_read
  let node' : ReconstructNodeMemoryCarrier
      (memory.write 736 second.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node size := ⟨source', hnode⟩
  have hintermediate : node'.source.image.sliceD 704 32 0 =
      intermediate.toBytes := by
    change (Bytes.writeAt h.node.source.image 736 second.toBytes).sliceD
      704 32 0 = intermediate.toBytes
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.intermediate_read
  let intermediate' : ReconstructIntermediateMemoryCarrier
      (memory.write 736 second.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate size := ⟨node', hintermediate⟩
  refine ⟨intermediate', ?_⟩
  change (Bytes.writeAt h.node.source.image 736 second.toBytes).sliceD
    736 32 0 = second.toBytes
  rw [show 32 = second.toBytes.length by rw [B256.length_toBytes]]
  exact Bytes.sliceD_writeAt _ _ _

theorem ReconstructRegistersMemoryCarrier.readSecond
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256} {size : Nat}
    (h : ReconstructRegistersMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node intermediate
      second size) :
    Bytes.toB256 (memory.read 736 32).1 = second := by
  rw [Mem.Reads.read h.intermediate.node.source.reads, h.second_read,
    B256.toB256_toBytes]

/-- Logical SHA expansion preserves all three digest registers. -/
def ReconstructRegistersMemoryCarrier.extendForHash
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256} {size : Nat}
    (h : ReconstructRegistersMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node intermediate
      second size)
    (inputWord outputWord : B256) :
    ReconstructRegistersMemoryCarrier
      (memory.extends (reconstructionShaWindows inputWord outputWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second
      (memExtsSize size (reconstructionShaWindows inputWord outputWord)) := by
  exact ⟨h.intermediate.extendForHash inputWord outputWord, h.second_read⟩

/-- The steady-state three-register carrier after staging words 0–1. -/
structure ReconstructPairMemoryCarrier
    (memory : Mem)
    (pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes)
    (oldCount amount node intermediate second left right : B256)
    (size : Nat) : Type where
  registers : ReconstructRegistersMemoryCarrier memory pubkeyInput
    signatureFirst signatureTail withdrawal amountPadded oldCount amount
    node intermediate second size
  shaInput : memory.data.sliceD 0 64 0 = left.toBytes ++ right.toBytes

/-- Stage a steady-state pair while retaining all three digest registers. -/
def ReconstructRegistersMemoryCarrier.stagePair
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256} {size : Nat}
    (h : ReconstructRegistersMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node intermediate
      second size)
    (left right : B256) (hfit : 64 ≤ size) :
    ReconstructPairMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 right.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second left right size := by
  let pair := h.intermediate.stagePair left right hfit
  have hsecond : pair.intermediate.node.source.image.sliceD 736 32 0 =
      second.toBytes := by
    change (Bytes.writeAt
      (Bytes.writeAt h.intermediate.node.source.image 0 left.toBytes)
      32 right.toBytes).sliceD 736 32 0 = second.toBytes
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega),
      Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
        rw [B256.length_toBytes]
        omega)]
    exact h.second_read
  let registers' : ReconstructRegistersMemoryCarrier
      ((memory.write 0 left.toBytes).write 32 right.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second size :=
    ⟨pair.intermediate, hsecond⟩
  exact ⟨registers', pair.shaInput⟩

/-- Replace word 20 while preserving words 22 and 23. -/
def ReconstructRegistersMemoryCarrier.writeNode
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256} {size : Nat}
    (h : ReconstructRegistersMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node intermediate
      second size)
    (node' : B256) (hfit : 672 ≤ size) :
    ReconstructRegistersMemoryCarrier (memory.write 640 node'.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node' intermediate second size := by
  let nextNode := h.intermediate.node.source.writeNode node' hfit
  have hintermediate : nextNode.source.image.sliceD 704 32 0 =
      intermediate.toBytes := by
    change (Bytes.writeAt h.intermediate.node.source.image 640 node'.toBytes).sliceD
      704 32 0 = intermediate.toBytes
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    exact h.intermediate.intermediate_read
  let nextIntermediate : ReconstructIntermediateMemoryCarrier
      (memory.write 640 node'.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node' intermediate size :=
    ⟨nextNode, hintermediate⟩
  have hsecond : nextIntermediate.node.source.image.sliceD 736 32 0 =
      second.toBytes := by
    change (Bytes.writeAt h.intermediate.node.source.image 640 node'.toBytes).sliceD
      736 32 0 = second.toBytes
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    exact h.second_read
  exact ⟨nextIntermediate, hsecond⟩

/-- Replace word 22 while preserving words 20 and 23. -/
def ReconstructRegistersMemoryCarrier.writeIntermediate
    {memory : Mem}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256} {size : Nat}
    (h : ReconstructRegistersMemoryCarrier memory pubkeyInput signatureFirst
      signatureTail withdrawal amountPadded oldCount amount node intermediate
      second size)
    (intermediate' : B256) (hfit : 736 ≤ size) :
    ReconstructRegistersMemoryCarrier (memory.write 704 intermediate'.toBytes)
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate' second size := by
  let nextIntermediate :=
    h.intermediate.node.writeIntermediate intermediate' hfit
  have hsecond : nextIntermediate.node.source.image.sliceD 736 32 0 =
      second.toBytes := by
    change (Bytes.writeAt h.intermediate.node.source.image 704
      intermediate'.toBytes).sliceD 736 32 0 = second.toBytes
    rw [Bytes.sliceD_writeAt_after_reconstruct _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    exact h.second_read
  exact ⟨nextIntermediate, hsecond⟩

end Blanc.BeaconDeposit
