import Blanc.Lift.UniswapV2Pair.GetterMemory
import Blanc.Lift.UniswapV2Pair.Execution
import Blanc.MemoryLayout
import Blanc.Lift.CopyLoop

/-! The two constant strings and their actual ordered memory stages. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive StringGetter where
  | name
  | symbol

def StringGetter.length : StringGetter → B256
  | .name => 10
  | .symbol => 6

def StringGetter.data : StringGetter → Bytes
  | .name => [0x55, 0x6e, 0x69, 0x73, 0x77, 0x61, 0x70, 0x20, 0x56, 0x32]
  | .symbol => [0x55, 0x4e, 0x49, 0x2d, 0x56, 0x32]

def StringGetter.word (s : StringGetter) : B256 :=
  Bytes.toB256 (s.data ++ List.replicate (32 - s.data.length) 0)

def StringGetter.entry : StringGetter → Entry
  | .name => .name
  | .symbol => .symbol

def StringGetter.selector : StringGetter → B256
  | .name => 0x06fdde03
  | .symbol => 0x95d89b41

def getterStringStage (L W : B256) : MemoryStage :=
  MemoryStage.words [(64, 192), (128, L), (160, W)]

def getterStringMemory (M : Mem) (L W : B256) : Mem :=
  (getterStringStage L W).applyMemory M

theorem getterStringMemory_ptr {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    PtrMem 192 192 (getterStringMemory M L W) := by
  have a : PtrMem 192 96 (M.write 64 (192 : B256).toBytes) := mem.set
  have b := a.write 128 L (Or.inr (by decide))
  rw [show memExtSize 96 128 32 = 160 from by decide] at b
  have c := b.write 160 W (Or.inr (by decide))
  rw [show memExtSize 160 160 32 = 192 from by decide] at c
  exact c

def getterStringHeadStage (L : B256) : MemoryStage :=
  MemoryStage.words [(192, 32), (224, L)]

def getterStringHeads (M : Mem) (L W : B256) : Mem :=
  (getterStringHeadStage L).applyMemory (getterStringMemory M L W)

def getterStringCopied (M : Mem) (L W : B256) : Mem :=
  (getterStringHeads M L W).write 256 W.toBytes

def getterStringFinalMemory (M : Mem) (L W : B256) : Mem :=
  (getterStringCopied M L W).write 256 W.toBytes

theorem getterStringHeads_ptr {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    PtrMem 192 256 (getterStringHeads M L W) := by
  have a := (getterStringMemory_ptr mem L W).write 192 32 (Or.inr (by decide))
  rw [show memExtSize 192 192 32 = 224 from by decide] at a
  have b := a.write 224 L (Or.inr (by decide))
  rw [show memExtSize 224 224 32 = 256 from by decide] at b
  exact b

theorem getterStringHeads_words {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    memWord (getterStringHeads M L W) 128 = L ∧
      memWord (getterStringHeads M L W) 160 = W := by
  let writes : List (Nat × B256) := [(64, 192), (128, L), (160, W), (192, 32), (224, L)]
  have reads := (MemoryStage.wf_reads (MemoryStage.words writes)
    mem.wf (Mem.reads_data M)).2
  change Mem.Reads (getterStringHeads M L W) ((MemoryStage.words writes).applyImage M.data.toList) at reads
  constructor
  · change Bytes.toB256 ((getterStringHeads M L W).read 128 32).1 = L
    rw [reads.read]
    have h := MemoryStage.read_written_word [(64, 192)] [(160, W), (192, 32), (224, L)]
      M.data.toList 128 L (by
        simp only [MemoryStage.words, List.map_cons, List.map_nil,
          MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
        rfl)
    simp only [List.cons_append, List.nil_append] at h
    rw [h]
    exact B256.toB256_toBytes L
  · change Bytes.toB256 ((getterStringHeads M L W).read 160 32).1 = W
    rw [reads.read]
    have h := MemoryStage.read_written_word [(64, 192), (128, L)] [(192, 32), (224, L)]
      M.data.toList 160 W (by
        simp only [MemoryStage.words, List.map_cons, List.map_nil,
          MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
        rfl)
    simp only [List.cons_append, List.nil_append] at h
    rw [h]
    exact B256.toB256_toBytes W

theorem getterStringCopied_ptr {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    PtrMem 192 288 (getterStringCopied M L W) := by
  have h := (getterStringHeads_ptr mem L W).write 256 W (Or.inr (by decide))
  rw [show memExtSize 256 256 32 = 288 from by decide] at h
  exact h

theorem getterStringCopied_word (M : Mem) (L W : B256) :
    memWord (getterStringCopied M L W) 256 = W :=
  (Mem.memWord_write_word (getterStringHeads M L W) 256 W).1


def getterStringHead1 (M : Mem) (L W : B256) : Mem :=
  (getterStringMemory M L W).write 192 (32 : B256).toBytes

theorem getterStringHead1_ptr {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    PtrMem 192 224 (getterStringHead1 M L W) := by
  have h := (getterStringMemory_ptr mem L W).write 192 32 (Or.inr (by decide))
  rw [show memExtSize 192 192 32 = 224 from by decide] at h
  exact h

theorem getterStringHead1_length {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    memWord (getterStringHead1 M L W) 128 = L := by
  let writes : List (Nat × B256) := [(64, 192), (128, L), (160, W), (192, 32)]
  have reads := (MemoryStage.wf_reads (MemoryStage.words writes)
    mem.wf (Mem.reads_data M)).2
  change Mem.Reads (getterStringHead1 M L W) ((MemoryStage.words writes).applyImage M.data.toList) at reads
  change Bytes.toB256 ((getterStringHead1 M L W).read 128 32).1 = L
  rw [reads.read]
  have h := MemoryStage.read_written_word [(64, 192)] [(160, W), (192, 32)]
    M.data.toList 128 L (by
      simp only [MemoryStage.words, List.map_cons, List.map_nil,
        MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
      rfl)
  simp only [List.cons_append, List.nil_append] at h
  rw [h]
  exact B256.toB256_toBytes L

def getterStringHeadImage (M : Mem) (L W : B256) : Bytes :=
  (MemoryStage.words [(64, 192), (128, L), (160, W), (192, 32), (224, L)]).applyImage M.data.toList


theorem getterStringHeads_reads {M : Mem} (mem : PtrMem 128 96 M) (L W : B256) :
    Mem.Reads (getterStringHeads M L W) (getterStringHeadImage M L W) := by
  have h := (MemoryStage.wf_reads
    (MemoryStage.words [(64, 192), (128, L), (160, W), (192, 32), (224, L)])
    mem.wf (Mem.reads_data M)).2
  exact h

def getterStringCopyImage (M : Mem) (L W : B256) : Bytes :=
  copyImg (getterStringHeadImage M L W) 160 256 1

def getterStringFinalImage (M : Mem) (L W : B256) : Bytes :=
  (MemoryStage.words [(64, 192), (128, L), (160, W), (192, 32), (224, L), (256, W), (256, W)]).applyImage M.data.toList

theorem getterStringCopyImage_stage (M : Mem) (L W : B256) :
    getterStringCopyImage M L W =
      (MemoryStage.words [(64, 192), (128, L), (160, W), (192, 32), (224, L), (256, W)]).applyImage M.data.toList := by
  have source := MemoryStage.read_written_word [(64, 192), (128, L)] [(192, 32), (224, L)]
    M.data.toList 160 W (by
      simp only [MemoryStage.words, List.map_cons, List.map_nil,
        MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
      rfl)
  simp only [List.cons_append, List.nil_append] at source
  simp only [getterStringCopyImage, copyImg, Nat.mul_one, getterStringHeadImage]
  rw [source]
  rfl

theorem getterStringFinalImage_read (M : Mem) (L W : B256) :
    (getterStringFinalImage M L W).sliceD 192 96 0 = encodeWords [32, L, W] := by
  unfold getterStringFinalImage
  have r0 := MemoryStage.read_written_word [(64, 192), (128, L), (160, W)]
    [(224, L), (256, W), (256, W)] M.data.toList 192 32 (by
      simp only [MemoryStage.words, List.map_cons, List.map_nil,
        MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
      rfl)
  have r1 := MemoryStage.read_written_word [(64, 192), (128, L), (160, W), (192, 32)]
    [(256, W), (256, W)] M.data.toList 224 L (by
      simp only [MemoryStage.words, List.map_cons, List.map_nil,
        MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
      rfl)
  have r2 := MemoryStage.read_written_word
    [(64, 192), (128, L), (160, W), (192, 32), (224, L), (256, W)]
    [] M.data.toList 256 W (by rfl)
  simp only [List.cons_append, List.nil_append] at r0 r1 r2
  rw [show (96 : Nat) = 32 + (32 + 32) from rfl, List.sliceD_add, List.sliceD_add]
  rw [r0, r1, r2]
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]

def getterStringPost (b : Devm) (R : List B256) (M : Mem) (L W : B256) (G : Nat) : Devm :=
  returnPost (St b (192 :: 96 :: R) (getterStringFinalMemory M L W) G) 192 96 R

theorem getterStringPost_facts {b : Devm} {R : List B256} {M : Mem} {L W : B256} {G : Nat}
    (mem : PtrMem 128 96 M) :
    (getterStringPost b R M L W G).output = encodeWords [32, L, W] ∧
      (∀ a, Devm.getStor (getterStringPost b R M L W G) a = Devm.getStor b a) ∧
      (getterStringPost b R M L W G).logs = b.logs ∧
      (getterStringPost b R M L W G).gasLeft = G := by
  refine ⟨?_, fun _ => rfl, rfl, rfl⟩
  let writes : List (Nat × B256) :=
    [(64, 192), (128, L), (160, W), (192, 32), (224, L), (256, W), (256, W)]
  have reads := (MemoryStage.wf_reads (MemoryStage.words writes)
    mem.wf (Mem.reads_data M)).2
  have memory_eq : (MemoryStage.words writes).applyMemory M = getterStringFinalMemory M L W := by
    simp only [writes, getterStringFinalMemory, getterStringCopied, getterStringHeads,
      getterStringMemory, getterStringStage, getterStringHeadStage, MemoryStage.words,
      MemoryStage.applyMemory, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [memory_eq] at reads
  rw [getterStringPost, (returnPost_facts
    (St b (192 :: 96 :: R) (getterStringFinalMemory M L W) G) 192 96 R).1]
  simp only [St.memory, show (192 : B256).toNat = 192 from rfl,
    show (96 : B256).toNat = 96 from rfl]
  rw [reads.read]
  exact getterStringFinalImage_read M L W


theorem getterStringCopy_memory_facts {M copied : Mem} (L W : B256)
    (wf : Mem.Wf copied) (reads : Mem.Reads copied (getterStringCopyImage M L W))
    (size : copied.size = 288) :
    PtrMem 192 288 copied ∧ memWord copied 256 = W ∧
      ((copied.write 256 W.toBytes).read 192 96).1 = encodeWords [32, L, W] := by
  have pointer := MemoryStage.read_written_word []
    [(128, L), (160, W), (192, 32), (224, L), (256, W)] M.data.toList 64 192 (by
      simp only [MemoryStage.words, List.map_cons, List.map_nil,
        MemoryStage.avoids, List.all_cons, List.all_nil, B256.length_toBytes]
      rfl)
  have payload := MemoryStage.read_written_word
    [(64, 192), (128, L), (160, W), (192, 32), (224, L)]
    [] M.data.toList 256 W (by rfl)
  simp only [List.cons_append, List.nil_append] at pointer payload
  refine ⟨⟨size, by decide, wf, ?_⟩, ?_, ?_⟩
  · intro o v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    cases hv
    refine ⟨by rw [size]; decide, ?_⟩
    change Bytes.toB256 (copied.read 64 32).1 = 192
    rw [reads.read, getterStringCopyImage_stage, pointer]
    exact B256.toB256_toBytes 192
  · change Bytes.toB256 (copied.read 256 32).1 = W
    rw [reads.read, getterStringCopyImage_stage, payload]
    exact B256.toB256_toBytes W
  · have padded := reads.write wf 256 W.toBytes
    have image_eq : Bytes.writeAt (getterStringCopyImage M L W) 256 W.toBytes =
        getterStringFinalImage M L W := by
      rw [getterStringCopyImage_stage]
      rfl
    rw [image_eq] at padded
    rw [padded.read, getterStringFinalImage_read]

theorem StringGetter.encode (s : StringGetter) :
    encodeWords [32, s.length, s.word] = encodeString s.data := by
  cases s <;> decide +kernel

theorem StringGetter.result (s : StringGetter) (st : State) :
    getterResult st s.entry = some (encodeWords [32, s.length, s.word]) := by
  rw [s.encode]
  cases s <;> rfl

theorem StringGetter.masked (s : StringGetter) :
    (~~~ (B256.bexp 256 (32 - s.length) - 1)) &&& s.word = s.word := by
  cases s <;> decide +kernel

end Blanc.Lift.UniswapV2Pair
