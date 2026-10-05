import Blanc.Lift.WalkSteps

/-! Reading back four consecutive word stores as one 128-byte window, the shape
of a four-word ABI event payload staged at the free pointer. -/
namespace Blanc.Lift
open Jaune

private theorem word_slice (bs : Bytes) (n : Nat) (v : B256) :
    (Bytes.writeAt bs n v.toBytes).sliceD n 32 0 = v.toBytes := by
  have h := Bytes.sliceD_writeAt bs v.toBytes n
  rw [B256.length_toBytes] at h
  exact h

/-- Four consecutive word stores read back as their concatenation. -/
theorem Mem.read_four_word_writes {μ : Mem} (wf : Mem.Wf μ) (s : Nat) (a b c d : B256) :
    (((((μ.write s a.toBytes).write (s + 32) b.toBytes).write (s + 64) c.toBytes).write
      (s + 96) d.toBytes).read s 128).1 = a.toBytes ++ b.toBytes ++ c.toBytes ++ d.toBytes := by
  have w1 := wf.write s a.toBytes
  have w2 := w1.write (s + 32) b.toBytes
  have w3 := w2.write (s + 64) c.toBytes
  have r := ((((Mem.reads_data μ).write wf s a.toBytes).write w1 (s + 32) b.toBytes).write w2
    (s + 64) c.toBytes).write w3 (s + 96) d.toBytes
  have la := B256.length_toBytes a
  have lb := B256.length_toBytes b
  have lc := B256.length_toBytes c
  rw [r.read, show (128 : Nat) = 32 + (32 + (32 + 32)) from rfl, List.sliceD_split,
    List.sliceD_split, List.sliceD_split]
  rw [Bytes.sliceD_writeAt_before _ _ s 32 (s + 96) (by omega),
    Bytes.sliceD_writeAt_before _ _ s 32 (s + 64) (by omega),
    Bytes.sliceD_writeAt_before _ _ s 32 (s + 32) (by omega), word_slice,
    Bytes.sliceD_writeAt_before _ _ (s + 32) 32 (s + 96) (by omega),
    Bytes.sliceD_writeAt_before _ _ (s + 32) 32 (s + 64) (by omega), word_slice,
    Bytes.sliceD_writeAt_before _ _ (s + 32 + 32) 32 (s + 96) (by omega),
    show s + 32 + 32 = s + 64 from by omega, word_slice,
    show s + 64 + 32 = s + 96 from by omega, word_slice]
  simp only [List.append_assoc]

end Blanc.Lift
