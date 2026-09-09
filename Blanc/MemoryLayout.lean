import Blanc.BytesWrite
import Blanc.ForwardCall
import Blanc.MemoryImage

/-!
# Ordered memory staging

Finite memory layouts are lists of exact byte writes in execution order.  The
same list acts on the symbolic byte image through `Bytes.writeAt` and on EVM
memory through `Mem.write`; overlap therefore has the machine's ordinary
last-write-wins meaning.  Footprints record byte spans, while allocation uses
`memExtsSize` and retains its word rounding and empty-write behavior.
-/

namespace Blanc

open Jaune

/-- An ordered list of byte offsets and exact payloads. -/
abbrev MemoryStage := List (Nat × Bytes)

namespace MemoryStage

/-- Apply the writes to a symbolic byte image, in list order. -/
def applyImage (stage : MemoryStage) (image : Bytes) : Bytes :=
  stage.foldl (fun current write =>
    Bytes.writeAt current write.1 write.2) image

/-- Apply the writes to actual EVM memory, in list order. -/
def applyMemory (stage : MemoryStage) (memory : Mem) : Mem :=
  stage.foldl (fun current write =>
    current.write write.1 write.2) memory

/-- Exact half-open byte footprints `(offset, payload length)`, in write order. -/
def footprint (stage : MemoryStage) : List (Nat × Nat) :=
  stage.map fun write => (write.1, write.2.length)

/-- Every write misses the selected half-open byte window. -/
def avoids (stage : MemoryStage) (offset width : Nat) : Bool :=
  stage.all fun write =>
    decide (offset + width ≤ write.1 ∨
      write.1 + write.2.length ≤ offset)

/-- Every selected window is missed by every write. -/
def avoidsAll (stage : MemoryStage) (windows : List (Nat × Nat)) : Bool :=
  windows.all fun window => stage.avoids window.1 window.2

/-- Every write ends at or below a suffix boundary. -/
def before (stage : MemoryStage) (start : Nat) : Bool :=
  stage.all fun write => decide (write.1 + write.2.length ≤ start)

@[simp] theorem applyImage_nil (image : Bytes) :
    applyImage [] image = image := rfl

@[simp] theorem applyImage_cons
    (write : Nat × Bytes) (stage : MemoryStage) (image : Bytes) :
    applyImage (write :: stage) image =
      applyImage stage (Bytes.writeAt image write.1 write.2) := rfl

@[simp] theorem applyMemory_nil (memory : Mem) :
    applyMemory [] memory = memory := rfl

@[simp] theorem applyMemory_cons
    (write : Nat × Bytes) (stage : MemoryStage) (memory : Mem) :
    applyMemory (write :: stage) memory =
      applyMemory stage (memory.write write.1 write.2) := rfl

theorem applyImage_append
    (first second : MemoryStage) (image : Bytes) :
    applyImage (first ++ second) image =
      applyImage second (applyImage first image) := by
  unfold applyImage
  rw [List.foldl_append]

theorem applyMemory_append
    (first second : MemoryStage) (memory : Mem) :
    applyMemory (first ++ second) memory =
      applyMemory second (applyMemory first memory) := by
  unfold applyMemory
  rw [List.foldl_append]

/-- Folding the two concrete write operations preserves their correspondence. -/
theorem wf_reads (stage : MemoryStage)
    {memory : Mem} {image : Bytes}
    (hwf : Mem.Wf memory) (hreads : Mem.Reads memory image) :
    Mem.Wf (stage.applyMemory memory) ∧
      Mem.Reads (stage.applyMemory memory) (stage.applyImage image) := by
  induction stage generalizing memory image with
  | nil => exact ⟨hwf, hreads⟩
  | cons write stage ih =>
      exact ih (hwf.write write.1 write.2)
        (Mem.Reads.write hwf hreads write.1 write.2)

/-- A finite guard is sound for padded symbolic slices. -/
theorem applyImage_sliceD_of_avoids
    (stage : MemoryStage) (image : Bytes) (offset width : Nat)
    (h : stage.avoids offset width = true) :
    (stage.applyImage image).sliceD offset width 0 =
      image.sliceD offset width 0 := by
  induction stage generalizing image with
  | nil => rfl
  | cons write stage ih =>
      simp only [avoids, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rw [applyImage_cons,
        ih (image := Bytes.writeAt image write.1 write.2) h.2]
      rcases h.1 with after | before
      · exact Bytes.sliceD_writeAt_before _ _ _ _ _ after
      · exact Bytes.sliceD_writeAt_after _ _ _ _ _ before

/-- A successful batch guard supplies the sound slice equation for each
listed observation. -/
theorem applyImage_slices_of_avoidsAll
    (stage : MemoryStage) (image : Bytes) (windows : List (Nat × Nat))
    (h : stage.avoidsAll windows = true) :
    ∀ window ∈ windows,
      (stage.applyImage image).sliceD window.1 window.2 0 =
        image.sliceD window.1 window.2 0 := by
  intro window hmem
  induction windows with
  | nil => simp at hmem
  | cons first rest ih =>
      simp only [avoidsAll, List.all_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hmem with rfl | later
      · exact stage.applyImage_sliceD_of_avoids image _ _ h.1
      · exact ih h.2 later

/-- Recover one selected write when every later write misses its exact window.
Earlier writes may overlap it. -/
theorem read_written
    (initial suffix : MemoryStage) (image payload : Bytes) (offset : Nat)
    (h : suffix.avoids offset payload.length = true) :
    ((initial ++ (offset, payload) :: suffix).applyImage image).sliceD
        offset payload.length 0 = payload := by
  rw [applyImage_append, applyImage_cons,
    applyImage_sliceD_of_avoids suffix _ offset payload.length h]
  exact Bytes.sliceD_writeAt _ _ _

/-- The exact image length after an ordered stage. -/
theorem applyImage_length (stage : MemoryStage) (image : Bytes) :
    (stage.applyImage image).length =
      stage.foldl (fun length write =>
        max length (write.1 + write.2.length)) image.length := by
  induction stage generalizing image with
  | nil => rfl
  | cons write stage ih =>
      rw [applyImage_cons, ih, Bytes.length_writeAt]
      rfl

/-- The exact allocated memory size follows the primitive multi-window fold. -/
theorem applyMemory_size (stage : MemoryStage) (memory : Mem)
    (haligned : memory.size % 32 = 0) :
    (stage.applyMemory memory).size =
      memExtsSize memory.size stage.footprint := by
  induction stage generalizing memory with
  | nil => rfl
  | cons write stage ih =>
      rw [applyMemory_cons, footprint, List.map_cons, memExtsSize]
      have hone : (memory.write write.1 write.2).size =
          memExtSize memory.size write.1 write.2.length :=
        Mem.size_write_of_size rfl haligned rfl
      have haligned' :
          (memory.write write.1 write.2).size % 32 = 0 := by
        rw [hone]
        exact memExtSize_mod_32 haligned
      rw [ih (memory := memory.write write.1 write.2)
        haligned', hone]
      rfl

/-- If every payload fits the initial allocation, the whole stage preserves
its size.  This is deliberately stronger than merely bounding byte footprints:
the premise mentions the actual allocated size. -/
theorem applyMemory_size_of_covered
    (stage : MemoryStage) (memory : Mem)
    (hcovered : ∀ write ∈ stage,
      write.1 + write.2.length ≤ memory.size) :
    (stage.applyMemory memory).size = memory.size := by
  induction stage generalizing memory with
  | nil => rfl
  | cons write stage ih =>
      have hhead := hcovered write (by simp)
      have hone : (memory.write write.1 write.2).size = memory.size :=
        Mem.size_write_of_le hhead
      rw [applyMemory_cons, ih]
      · exact hone
      · intro later hlater
        rw [hone]
        exact hcovered later (by simp [hlater])

/-- Turn an ordered list of word stores into an exact byte stage. -/
def words (writes : List (Nat × B256)) : MemoryStage :=
  writes.map fun write => (write.1, write.2.toBytes)

@[simp] theorem footprint_words (writes : List (Nat × B256)) :
    (words writes).footprint = writes.map fun write => (write.1, 32) := by
  simp [words, footprint, List.map_map, Function.comp_def,
    B256.length_toBytes]

/-- Word stages expose allocation directly as 32-byte windows. -/
theorem applyMemory_words_size (writes : List (Nat × B256)) (memory : Mem)
    (haligned : memory.size % 32 = 0) :
    ((words writes).applyMemory memory).size =
      memExtsSize memory.size (writes.map fun write => (write.1, 32)) := by
  rw [applyMemory_size _ _ haligned, footprint_words]

/-- Symbolic image length for a word stage has exact 32-byte footprints. -/
theorem applyImage_words_length
    (writes : List (Nat × B256)) (image : Bytes) :
    ((words writes).applyImage image).length =
      writes.foldl (fun length write =>
        max length (write.1 + 32)) image.length := by
  induction writes generalizing image with
  | nil => rfl
  | cons write writes ih =>
      rw [show words (write :: writes) =
        (write.1, write.2.toBytes) :: words writes by rfl,
        applyImage_cons, ih, Bytes.length_writeAt,
        B256.length_toBytes]
      rfl

/-- Word-sized read-back specialization used by fixed ABI and scratch layouts. -/
theorem read_written_word
    (initial suffix : List (Nat × B256))
    (image : Bytes) (offset : Nat) (word : B256)
    (h : (words suffix).avoids offset 32 = true) :
    ((words (initial ++ (offset, word) :: suffix)).applyImage image).sliceD
        offset 32 0 = word.toBytes := by
  have read := read_written (words initial) (words suffix)
    image word.toBytes offset (by simpa only [B256.length_toBytes] using h)
  simpa only [words, List.map_append, List.map_cons,
    B256.length_toBytes] using read

/-- Stages confined below a boundary compose with the existing suffix frame. -/
theorem wordFrameFrom
    (stage : MemoryStage) (image : Bytes) (start : Nat)
    (h : stage.before start = true) :
    Bytes.WordFrameFrom image (stage.applyImage image) start := by
  induction stage generalizing image with
  | nil => exact Bytes.WordFrameFrom.refl image start
  | cons write stage ih =>
      simp only [before, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at h
      exact (Bytes.WordFrameFrom.writeBefore
          (Bytes.WordFrameFrom.refl image start)
          write.1 write.2 h.1).trans
        (ih (image := Bytes.writeAt image write.1 write.2) h.2)

/-! ## Executable boundary controls -/

/-- Distinct overlapping payloads make the order observable. -/
theorem control_overlap_order_matters :
    applyImage ([(0, [1]), (0, [2])] : MemoryStage) [] ≠
      applyImage ([(0, [2]), (0, [1])] : MemoryStage) [] := by
  decide +kernel

/-- An earlier overlap is allowed; the chosen write is recovered because its
later suffix misses it. -/
theorem control_read_written_allows_earlier_overlap :
    (applyImage ([(0, [1, 1]), (0, [2, 3]), (2, [4])] : MemoryStage)
        []).sliceD 0 2 0 = [2, 3] := by
  exact read_written [(0, [1, 1])] [(2, [4])] [] [2, 3] 0 (by decide +kernel)

/-- A later overlapping write is rejected by the finite window guard. -/
theorem control_overlap_guard_rejects :
    avoids ([(0, [1]), (1, [2])] : MemoryStage) 0 2 = false := by
  decide +kernel

/-- Covered-size preservation cannot be invoked for a write beyond the given
allocation. -/
theorem control_out_of_allocation_not_covered :
    ¬ (∀ write ∈ ([(32, [1])] : MemoryStage),
      write.1 + write.2.length ≤ 32) := by
  decide +kernel

/-- An empty image write pads to its offset, and a later byte write overlays
that padded image, exactly as `Bytes.writeAt` specifies. -/
theorem control_empty_and_padded_image :
    applyImage ([(5, []), (2, [7])] : MemoryStage) [] =
      [0, 0, 7, 0, 0] := by
  decide +kernel

/-- A one-byte write at offset 33 allocates two EVM words. -/
theorem control_allocation_rounding :
    (applyMemory ([(33, [7])] : MemoryStage) Mem.empty).size = 64 := by
  rw [applyMemory_size _ _ (by decide +kernel)]
  decide +kernel

end MemoryStage

/-- Apply a stage through the existing proof-carrying whole-image API. -/
theorem MemImage.applyStage
    {a b : Devm} {image : Bytes} (stage : MemoryStage)
    (source : MemImage a image)
    (memory : b.memory = stage.applyMemory a.memory) :
    MemImage b (stage.applyImage image) := by
  obtain ⟨hwf, hreads⟩ := source
  obtain ⟨hwf', hreads'⟩ := MemoryStage.wf_reads stage hwf hreads
  exact ⟨by rw [memory]; exact hwf', by rw [memory]; exact hreads'⟩

/-- A selected word crosses a finite stage whose guard proves every write
misses it. -/
theorem MemWordAt.applyStage
    {a b : Devm} {image : Bytes} {offset : Nat} {word : B256}
    (stage : MemoryStage) (source : MemImage a image)
    (memory : b.memory = stage.applyMemory a.memory)
    (h : stage.avoids offset 32 = true)
    (window : MemWordAt a offset word) : MemWordAt b offset word := by
  refine window.of_preserved_memImage source.2
    (MemImage.applyStage stage source memory) ?_
  exact MemoryStage.applyImage_sliceD_of_avoids
    stage image offset 32 h

end Blanc
