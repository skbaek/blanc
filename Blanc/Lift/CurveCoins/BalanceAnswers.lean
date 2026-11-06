import Blanc.Lift.DaiFrames
import Blanc.Lift.CurveCoins.DaiLocality
import Blanc.Lift.WordImage

/-!
# What a coin's `balanceOf` answers

The pool reads its own credit, and `donate_admin_fees` its books, from these replies: each is the entry it names, as that
code reads it.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The scratch hash with its base word stored first, as solc's public mapping getter does. -/
theorem keccak_base_first {μ : Mem} (wf : Mem.Wf μ) (base key : B256) :
    (((μ.write (Bytes.toB256 [32]).toNat base.toBytes).write (Bytes.toB256 [0]).toNat key.toBytes).read
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).1.keccak = mapSlot key base := by
  have l0 : (Bytes.toB256 [0]).toNat = 0 := by decide +kernel
  have l32 : (Bytes.toB256 [32]).toNat = 32 := by decide +kernel
  have l64 : (Bytes.toB256 [64]).toNat = 64 := by decide +kernel
  rw [l0, l32, l64]
  have e : (((μ.write 32 base.toBytes).write 0 key.toBytes).read 0 64).1 = key.toBytes ++ base.toBytes := by
    have w1 := wf.write 32 base.toBytes
    have r := ((Mem.reads_data μ).write wf 32 base.toBytes).write w1 0 key.toBytes
    have hs : ∀ (bs : Bytes) (n : Nat) (v : B256),
        (Bytes.writeAt bs n v.toBytes).sliceD n 32 0 = v.toBytes := fun bs n v => by
      have h := Bytes.sliceD_writeAt bs v.toBytes n
      rw [B256.length_toBytes] at h
      exact h
    rw [r.read, show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split, hs,
      Bytes.sliceD_writeAt_word_after _ 0 (0 + 32) 32 key (by omega), hs]
  exact congrArg Bytes.keccak e

/-- **The `balanceOf(a)` frame of DAI answers `a`'s entry.** -/
theorem frame_balanceOf_output {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x70a08231)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    post.output = ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 29 t_128f_c29
  have h2 := hc.cut
  clear hc
  repeat ustep h2
  obtain ⟨_, e⟩ := ric_ret h2
  clear h2
  cases e
  repeat ustep h
  simp only [ff20_and_word, lit4] at h
  have wM1 : Mem.Wf (M.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes) := by uwf
  have l0 : (Bytes.toB256 [0]).toNat = 0 := by decide +kernel
  have l32 : (Bytes.toB256 [32]).toNat = 32 := by decide +kernel
  have l64 : (Bytes.toB256 [64]).toNat = 64 := by decide +kernel
  have l128 : (Bytes.toB256 [128]).toNat = 128 := by decide +kernel
  rw [keccak_base_first wM1, show mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 (Bytes.toB256 [2]) =
    balSlot (Sevm.dataWord sevm 4).toAdr from rfl] at h
  generalize hW : ((M.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes).write (Bytes.toB256 [32]).toNat
    (Bytes.toB256 [2]).toBytes).write (Bytes.toB256 [0]).toNat (Sevm.dataWord sevm 4).toAdr.toB256.toBytes = W at h
  have wW : Mem.Wf W := by
    rw [← hW]
    uwf
  have fp : (W.read (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [128]).toBytes := by
    rw [← hW, l0, l32, l64, Mem.read_write_word_disjoint (by uwf) 0 _ (.inl (by omega)),
      Mem.read_write_word_disjoint (by uwf) 32 _ (.inl (by omega))]
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
      show (Bytes.toB256 [32] + Bytes.toB256 [128] - Bytes.toB256 [128]).toNat = 32 by decide +kernel]
    rw [Mem.read_write_word_of_wf wN 128 v, ← hv]
    rfl

end Blanc.Lift.Dai

namespace Blanc.Lift.CurveCoins.Dai

open Jaune Blanc Blanc.Lift Blanc.Lift.Dai

/-- **`balanceOf`'s answer is the entry it names.** -/
theorem frame_balanceOf_answer {T : Adr} {F : Exec.Frame} (good : CodeFrame T HistFork code F)
    (target : F.sevm.currentTarget = T) (wf : Mem.Wf F.pre.memory) (sel : Blanc.Sevm.selector F.sevm = 0x70a08231) :
    F.post.output = (wordsAt T F.pre.state (balSlot (Sevm.dataWord F.sevm 4).toAdr)).toBytes := by
  have e := frame_balanceOf_output good.2.2.1 wf sel
    (run_of_frame cert_check rfl good.1 good.2.1 good.2.2.1.stateGas_none)
  simp only [target] at e
  exact e

end Blanc.Lift.CurveCoins.Dai
