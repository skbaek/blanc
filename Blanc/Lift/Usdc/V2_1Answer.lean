import Blanc.Lift.Usdc.V2_1Frames
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.WordImage

namespace Blanc.Lift.Usdc.ImplV2_1

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **The `balanceOf(a)` frame of FiatTokenV2_1 answers `a`'s word.** -/
theorem frame_balanceOf_output {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x70a08231)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    post.output = (b.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 39 t_2798_c39
  have h2 := hc.cut
  clear hc
  repeat ustep h2
  obtain ⟨_, e⟩ := ric_ret h2
  clear h2
  cases e
  repeat ustep h
  simp only [ff20_and_word, toAdr_toB256, show Bytes.toB256 [4] = 4 by decide] at h
  have wM1 : Mem.Wf (M.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes) := by uwf
  have l0 : (Bytes.toB256 [0]).toNat = 0 := by decide +kernel
  have l32 : (Bytes.toB256 [32]).toNat = 32 := by decide +kernel
  have l64 : (Bytes.toB256 [64]).toNat = 64 := by decide +kernel
  have l128 : (Bytes.toB256 [128]).toNat = 128 := by decide +kernel
  rw [keccak_scratch, show mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 (Bytes.toB256 [9]) =
    balSlot (Sevm.dataWord sevm 4).toAdr from rfl] at h
  generalize hW : ((M.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes).write (Bytes.toB256 [0]).toNat
    (Sevm.dataWord sevm 4).toAdr.toB256.toBytes).write (Bytes.toB256 [32]).toNat (Bytes.toB256 [9]).toBytes = W at h
  have wW : Mem.Wf W := by
    rw [← hW]
    uwf
  have fp : (W.read (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [128]).toBytes := by
    rw [← hW, l0, l32, l64, Mem.read_write_word_disjoint (by uwf) 32 _ (.inl (by omega)),
      Mem.read_write_word_disjoint (by uwf) 0 _ (.inl (by omega))]
    exact Mem.read_write_word_of_wf wf 64 _
  have w128 : (Bytes.toB256 [128]).toBytes.toB256 = Bytes.toB256 [128] := by decide +kernel
  simp only [memRead_snd_fst, fp, w128, l128] at h
  generalize hv : b.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr) = v at h
  have wN : Mem.Wf ((W.read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).2.read (Bytes.toB256 [64]).toNat 32).2 := by
    uwf
  have r2 : ((((W.read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).2.read (Bytes.toB256 [64]).toNat 32).2.write
      128 v.toBytes).read (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [128]).toBytes := by
    rw [Mem.read_write_word_disjoint wN 128 v (.inr (by rw [l64]; omega)), memRead_snd_fst, memRead_snd_fst, fp]
  rw [r2, w128] at h
  cases h with
  | last hl =>
    rw [(ri_return hl).1, memRead_snd_fst, l128,
      show (Bytes.toB256 [32] + (Bytes.toB256 [128] - Bytes.toB256 [128])).toNat = 32 by decide +kernel]
    rw [Mem.read_write_word_of_wf wN 128 v, ← hv]

end Blanc.Lift.Usdc.ImplV2_1
