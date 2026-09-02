-- MemoryImage.lean : proof-carrying memory images and selected word windows.

import Blanc.Ladder

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

/-!
# Proof-carrying memory windows

`MemImage` carries the structural invariant and reader image needed by
Blanc's memory-write algebra. `MemWordAt` forgets the rest of that image and
retains one exact 32-byte window, which is the useful frame invariant when a
long-lived word must cross unrelated scratch-memory traffic.

These carriers were first developed for the Lido CircuitBreaker proofs. They
are contract-independent: PRORATA's full-width arithmetic uses the same
window transport to preserve long-lived operation words above its scratch
region.
-/

/-- A concrete memory image, with the structural invariant the write algebra
needs. `Mem.Wf` rules out `Array.copyD` truncation, so it travels beside the
image rather than being re-derived at each write. -/
def MemImage (devm : Devm) (img : Bytes) : Prop :=
  Mem.Wf devm.memory ∧ Mem.Reads devm.memory img

/-- `target` agrees with `source` on every whole-word window beginning at or
above `start`. This is the compositional frame fact exposed by scratch-memory
traces whose writes are confined below a fixed boundary. -/
def Bytes.WordFrameFrom (source target : Bytes) (start : Nat) : Prop :=
  ∀ offset, start ≤ offset →
    target.sliceD offset 32 0 = source.sliceD offset 32 0

theorem Bytes.WordFrameFrom.refl (image : Bytes) (start : Nat) :
    Bytes.WordFrameFrom image image start := by
  intro offset _
  rfl

theorem Bytes.WordFrameFrom.trans
    {first second third : Bytes} {start : Nat}
    (firstToSecond : Bytes.WordFrameFrom first second start)
    (secondToThird : Bytes.WordFrameFrom second third start) :
    Bytes.WordFrameFrom first third start := by
  intro offset after
  exact (secondToThird offset after).trans (firstToSecond offset after)

theorem MemImage.of_memory_eq {a b : Devm} {img : Bytes}
    (h : b.memory = a.memory) (image : MemImage a img) : MemImage b img := by
  obtain ⟨hwf, hreads⟩ := image
  exact ⟨by rw [h]; exact hwf, by rw [h]; exact hreads⟩

theorem MemImage.write {a b : Devm} {img ys : Bytes} {n : Nat}
    (image : MemImage a img) (h : b.memory = a.memory.write n ys) :
    MemImage b (Bytes.writeAt img n ys) := by
  obtain ⟨hwf, hreads⟩ := image
  exact ⟨by rw [h]; exact hwf.write n ys,
    by rw [h]; exact Mem.Reads.write hwf hreads n ys⟩

/-- Memory reads the word `w` at byte offset `offset`. The backing image stays
existential, keeping large scratch areas out of downstream goals. -/
def MemWordAt (devm : Devm) (offset : Nat) (w : B256) : Prop :=
  Mem.Wf devm.memory ∧
    ∃ img : Bytes, Mem.Reads devm.memory img ∧
      img.sliceD offset 32 0 = w.toBytes

theorem MemWordAt.of_memImage {a : Devm} {img : Bytes} {offset : Nat}
    {w : B256} (image : MemImage a img)
    (hslice : img.sliceD offset 32 0 = w.toBytes) :
    MemWordAt a offset w := ⟨image.1, img, image.2, hslice⟩

/-- Any proof-carrying image of the same memory observes the selected word. -/
theorem MemWordAt.slice_eq {a : Devm} {img : Bytes} {offset : Nat}
    {w : B256} (window : MemWordAt a offset w)
    (reads : Mem.Reads a.memory img) :
    img.sliceD offset 32 0 = w.toBytes := by
  obtain ⟨_, source, sourceReads, sourceSlice⟩ := window
  rw [← Mem.Reads.read reads, Mem.Reads.read sourceReads]
  exact sourceSlice

/-- Transport a selected word to a new proof-carrying image whose relevant
slice is known to agree with an image of the source memory. -/
theorem MemWordAt.of_preserved_memImage
    {a b : Devm} {source target : Bytes} {offset : Nat} {w : B256}
    (window : MemWordAt a offset w)
    (sourceReads : Mem.Reads a.memory source)
    (targetImage : MemImage b target)
    (preserved : target.sliceD offset 32 0 =
      source.sliceD offset 32 0) :
    MemWordAt b offset w := by
  apply MemWordAt.of_memImage targetImage
  rw [preserved]
  exact window.slice_eq sourceReads

/-- Transport a selected word through a compositional frame relation. -/
theorem MemWordAt.of_wordFrame
    {a b : Devm} {source target : Bytes} {start offset : Nat} {w : B256}
    (window : MemWordAt a offset w)
    (sourceReads : Mem.Reads a.memory source)
    (targetImage : MemImage b target)
    (frame : Bytes.WordFrameFrom source target start)
    (after : start ≤ offset) :
    MemWordAt b offset w :=
  window.of_preserved_memImage sourceReads targetImage (frame offset after)

/-- The window a write creates: reading a word straight back at the offset it
was written to, whatever the image was before. -/
theorem MemWordAt.of_write {a b : Devm} {img : Bytes} {n : Nat} {w : B256}
    (image : MemImage a img) (h : b.memory = a.memory.write n w.toBytes) :
    MemWordAt b n w := by
  refine MemWordAt.of_memImage (image.write h) ?_
  have slice := Bytes.sliceD_writeAt img w.toBytes n
  rwa [B256.length_toBytes] at slice

theorem MemWordAt.of_memory_eq {a b : Devm} {offset : Nat} {w : B256}
    (h : b.memory = a.memory) (window : MemWordAt a offset w) :
    MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  exact ⟨by rw [h]; exact hwf, img, by rw [h]; exact hreads, hslice⟩

theorem MemWordAt.extend {a b : Devm} {offset : Nat} {w : B256} {i n : Nat}
    (h : b.memory = a.memory.extend i n) (window : MemWordAt a offset w) :
    MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  exact ⟨by rw [h]; exact hwf.extend i n, img,
    by rw [h]; exact hreads.extend i n, hslice⟩

/-- Cross a batch of logical memory extensions. Extensions grow the allocated
memory but do not move or replace any existing byte. -/
theorem MemWordAt.extends {a b : Devm} {offset : Nat} {w : B256}
    {pairs : List (Nat × Nat)}
    (h : b.memory = a.memory.extends pairs)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  exact ⟨by rw [h]; exact hwf.extends pairs, img,
    by rw [h]; exact hreads.extends pairs, hslice⟩

/-- A byte write whose complete span misses the selected word leaves that
word unchanged. Unlike `writeMiss`, this form is not restricted to a
32-byte source and is therefore suitable for CALL-family return windows. -/
theorem MemWordAt.writeMissBytes
    {a b : Devm} {offset : Nat} {w : B256} {ys : Bytes} {n : Nat}
    (h : b.memory = a.memory.write n ys)
    (miss : offset + 32 ≤ n ∨ n + ys.length ≤ offset)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  refine ⟨by rw [h]; exact hwf.write n ys, Bytes.writeAt img n ys,
    by rw [h]; exact Mem.Reads.write hwf hreads n ys, ?_⟩
  rcases miss with late | early
  · rw [Bytes.sliceD_writeAt_before img ys offset 32 n late]
    exact hslice
  · rw [Bytes.sliceD_writeAt_after img ys offset 32 n early]
    exact hslice

/-- The complete CALL-resume memory shape: first extend the parent's logical
memory for the declared windows, then copy a bounded byte string. Any word
outside the copied span survives independently of callee behaviour. -/
theorem MemWordAt.extendsWrite
    {a b : Devm} {offset : Nat} {w : B256}
    {pairs : List (Nat × Nat)} {ys : Bytes} {n : Nat}
    (h : b.memory = (a.memory.extends pairs).write n ys)
    (miss : offset + 32 ≤ n ∨ n + ys.length ≤ offset)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  have hwf' : Mem.Wf (a.memory.extends pairs) := hwf.extends pairs
  have hreads' : Mem.Reads (a.memory.extends pairs) img :=
    hreads.extends pairs
  refine ⟨by rw [h]; exact hwf'.write n ys, Bytes.writeAt img n ys,
    by rw [h]; exact Mem.Reads.write hwf' hreads' n ys, ?_⟩
  rcases miss with late | early
  · rw [Bytes.sliceD_writeAt_before img ys offset 32 n late]
    exact hslice
  · rw [Bytes.sliceD_writeAt_after img ys offset 32 n early]
    exact hslice

/-- Any selected word beyond a STATICCALL's declared output window survives
the instruction, on both the immediate-failure and successful-child resume
paths.  The callee output is unconstrained: `take os` alone bounds the copied
span. -/
theorem MemWordAt.acrossStaticcall
    {sevm : Sevm} {pre post : Devm} {offset : Nat} {w : B256}
    {g target inputOffset inputSize outputOffset outputSize : B256}
    {tail : Stack}
    (afterOutput : outputOffset.toNat + outputSize.toNat ≤ offset)
    (stack :
      g :: target :: inputOffset :: inputSize :: outputOffset :: outputSize ::
        tail <<+ pre.stack)
    (run : Ninst.Run sevm pre Ninst.staticcall post)
    (window : MemWordAt pre offset w) : MemWordAt post offset w := by
  rcases of_run_staticcall_val_with_depth stack run with failure | success
  · rcases failure with ⟨-, -, out, -, finalMemory⟩
    refine window.extendsWrite finalMemory (Or.inr ?_)
    have copiedLe : (out.take outputSize.toNat).length ≤ outputSize.toNat :=
      List.length_take_le _ _
    omega
  · rcases success with
      ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -,
        -, -, -, finalMemory, -⟩
    have memoryShape : post.memory =
        (pre.memory.extends
          [(inputOffset.toNat, inputSize.toNat),
            (outputOffset.toNat, outputSize.toNat)]).write
          outputOffset.toNat (child.output.take outputSize.toNat) := by
      rw [finalMemory, parentMemory]
    refine window.extendsWrite memoryShape (Or.inr ?_)
    have copiedLe :
        (child.output.take outputSize.toNat).length ≤ outputSize.toNat :=
      List.length_take_le _ _
    omega

/-- A whole-word write that lands entirely before or after the selected
window leaves it unchanged. -/
theorem MemWordAt.writeMiss {a b : Devm} {offset : Nat} {w v : B256}
    {n : Nat}
    (h : b.memory = a.memory.write n v.toBytes)
    (miss : offset + 32 ≤ n ∨ n + 32 ≤ offset)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  refine ⟨by rw [h]; exact hwf.write n v.toBytes,
    Bytes.writeAt img n v.toBytes,
    by rw [h]; exact Mem.Reads.write hwf hreads n v.toBytes, ?_⟩
  rcases miss with late | early
  · rw [Bytes.sliceD_writeAt_before img v.toBytes offset 32 n late]
    exact hslice
  · rw [Bytes.sliceD_writeAt_after img v.toBytes offset 32 n
      (by rw [B256.length_toBytes]; exact early)]
    exact hslice

/-- Forget a selected word down to any proof-carrying image of its memory. -/
theorem MemWordAt.memImage {a : Devm} {offset : Nat} {w : B256}
    (window : MemWordAt a offset w) : ∃ img : Bytes, MemImage a img := by
  obtain ⟨hwf, img, hreads, _⟩ := window
  exact ⟨img, hwf, hreads⟩

/-- `mstoreAt k` writes at its constant word offset; the stored value is
existential when only framing is relevant. -/
theorem of_run_mstoreAt_mem {e : Sevm} {s s' : Devm} {k : B256}
    (h : Line.Run e s (mstoreAt k) s') :
    ∃ v : B256, s'.memory = s.memory.write (k * 32).toNat v.toBytes := by
  rcases Line.of_run_cons h with ⟨_u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨_u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  rcases of_run_mstore_val qm with ⟨x, y, hpop, hm⟩
  have hx : (k * 32) = x :=
    (List.of_cons_pref_of_cons_pref (prefix_of_push hpb nil_pref)
      (pref_of_split hpop)).left
  exact ⟨y, by rw [hm, ← hx, ← hpb.memory]⟩

/-- The standard fixed-word `MLOAD` line changes memory only by logical
extension.  The theorem is stated against the literal shared line shape so
contract-local aliases such as `loadWord` remain definitionally compatible. -/
theorem of_run_loadWord_mem {e : Sevm} {s s' : Devm} {k : B256}
    (h : Line.Run e s [pushB256 (k * 32), mload] s') :
    ∃ i : Nat, s'.memory = s.memory.extend i 32 := by
  rcases Line.of_run_cons h with ⟨_u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨_u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  rcases of_run_mload_val qm with ⟨x, _, hm, _⟩
  exact ⟨x.toNat, by rw [hm, ← hpb.memory]⟩

/-- Cross a memory-silent line. -/
theorem MemWordAt.acrossLine {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} {l : Line} (inv : Line.Inv Devm.memory l)
    (run : Line.Run e a l b) (window : MemWordAt a offset w) :
    MemWordAt b offset w :=
  MemWordAt.of_memory_eq (Line.of_inv Devm.memory inv run).symm window

/-- Cross the standard fixed-word `MLOAD` line, forgetting the loaded value. -/
theorem MemWordAt.acrossLoadWord {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256} (run : Line.Run e a [pushB256 (k * 32), mload] b)
    (window : MemWordAt a offset w) : MemWordAt b offset w :=
  let ⟨_, hm⟩ := of_run_loadWord_mem run
  MemWordAt.extend hm window

/-- Cross `mstoreAt k` when the write misses the selected window. -/
theorem MemWordAt.acrossMstoreAt {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256}
    (miss : offset + 32 ≤ (k * 32).toNat ∨
      (k * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a (mstoreAt k) b)
    (window : MemWordAt a offset w) : MemWordAt b offset w :=
  let ⟨_, hm⟩ := of_run_mstoreAt_mem run
  MemWordAt.writeMiss hm miss window

/-- Cross one instruction with a registered memory invariant. -/
theorem MemWordAt.acrossNinst {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} {i : Ninst} [inst : Ninst.Hinv Devm.memory i]
    (run : Ninst.Run e a i b) (window : MemWordAt a offset w) :
    MemWordAt b offset w :=
  MemWordAt.of_memory_eq (inst.inv run).symm window

/-- Cross one bare `MLOAD`. -/
theorem MemWordAt.acrossMload {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Ninst.Run e a Ninst.mload b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨_x, _, hm, _⟩ := of_run_mload_val run
  exact MemWordAt.extend hm window

/-- Cross a `LOG`, which reads and logically extends memory without changing
the backing bytes. -/
theorem MemWordAt.acrossLogWith {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} {k : Fin 4} {x y : B256}
    (run : Line.Run e a (logWith k x y) b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold logWith at run
  rcases Line.of_run_cons run with ⟨_s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨_s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨_s3, q3, hnil⟩
  cases hnil
  obtain ⟨_mi, _sz, hm⟩ := of_run_log_mem q3
  exact MemWordAt.extend hm (MemWordAt.of_memory_eq
    ((of_run_pushB256 q1).memory.trans (of_run_pushB256 q2).memory).symm
      window)

/-- Read a selected window back through the standard fixed-word `MLOAD`
line. -/
theorem prefix_of_loadWord_window {e : Sevm} {s s' : Devm} {k w : B256}
    {xs : Stack} (window : MemWordAt s (k * 32).toNat w)
    (hp : xs <<+ s.stack)
    (run : Line.Run e s [pushB256 (k * 32), mload] s') :
    w :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨u, qp, run'⟩
  rcases Line.of_run_cons run' with ⟨_u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  obtain ⟨_hwf, img, hreads, hslice⟩ := window
  have hreads' : Mem.Reads u.memory img := by
    rw [← hpb.memory]
    exact hreads
  obtain ⟨hstack, _, _⟩ :=
    prefix_of_mload_val qm (prefix_of_push hpb hp) hreads'
  rw [hslice, B256.toB256_toBytes] at hstack
  exact hstack

end Blanc
