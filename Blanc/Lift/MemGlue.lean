import Blanc.Lift.Vyper
import Blanc.Lift.VyperFrameLoop

/-!
# Memory glue across a crossed callee

A callee crossed by `xa_node`/`xa_node_span` exports what it does to memory as
`Mem.KeepsOff M M' W`: memory does not shrink, and every byte off the windows `W` (half-open
`[lo, hi)` pairs) reads as before.  This module carries a caller's memory facts across it:

* `Mem.Reads.keepsOff`: a byte image of `M` gives one of `M'` that agrees with it off `W`;
* `Words.keepsOff`, `MemMatches.keepsOff`: carried words and recorded map words that miss `W`
  survive;
* `Mem.KeepsOff.refl`/`trans`/`mono`/`of_agreeOutside`: composing callee exports.

It also holds the generic memory-read algebra of the 3pool's quiet walks (hoisted from
`Blanc/Lift/Curve3Pool/Walk/Quiet.lean`).  Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Reads after writes -/

theorem memRead_snd_fst (μ : Mem) (i n j m : Nat) :
    ((μ.read i n).2.read j m).1 = (μ.read j m).1 :=
  rfl

theorem Mem.read_snd_eq (μ : Mem) (i n : Nat) : (μ.read i n).2 = μ.extend i n := rfl

theorem Mem.extend_read_fst (μ : Mem) (i n j m : Nat) :
    ((μ.extend i n).read j m).1 = (μ.read j m).1 := rfl

theorem Mem.extends_read_fst (μ : Mem) (l : List (Nat × Nat)) (a n : Nat) :
    ((μ.extends l).read a n).1 = (μ.read a n).1 := rfl

/-- Two consecutive word stores into a well-formed memory read back as one 64-byte window. -/
theorem Mem.read_two_word_writes_wf {μ : Mem} (wf : Mem.Wf μ) (s : Nat) (a c : B256) :
    (((μ.write s a.toBytes).write (s + 32) c.toBytes).read s 64).1 = a.toBytes ++ c.toBytes := by
  have w1 := wf.write s a.toBytes
  have r := ((Mem.reads_data μ).write wf s a.toBytes).write w1 (s + 32) c.toBytes
  have hs : ∀ (bs : Bytes) (n : Nat) (v : B256),
      (Bytes.writeAt bs n v.toBytes).sliceD n 32 0 = v.toBytes := fun bs n v => by
    have h := Bytes.sliceD_writeAt bs v.toBytes n
    rw [B256.length_toBytes] at h
    exact h
  rw [r.read, show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split,
    Bytes.sliceD_writeAt_before _ _ s 32 (s + 32) (by omega), hs, hs]

/-- Two consecutive word stores read back as one 64-byte window (offsets as numerals). -/
theorem Mem.read_two_word_writes_wf' {μ : Mem} (wf : Mem.Wf μ) {s t : Nat} (ht : t = s + 32)
    (a c : B256) :
    (((μ.write s a.toBytes).write t c.toBytes).read s 64).1 = a.toBytes ++ c.toBytes := by
  subst ht; exact Mem.read_two_word_writes_wf wf s a c

theorem Mem.read_split (μ : Mem) (a m n : Nat) :
    (μ.read a (m + n)).1 = (μ.read a m).1 ++ (μ.read (a + m) n).1 := by
  rw [(Mem.reads_data μ).read, (Mem.reads_data μ).read, (Mem.reads_data μ).read,
    List.sliceD_split]

/-- A 64-byte window reads as its two words. -/
theorem Mem.read_split64 (μ : Mem) {s t : Nat} (ht : t = s + 32) :
    (μ.read s 64).1 = (μ.read s 32).1 ++ (μ.read t 32).1 := by
  subst ht
  exact Mem.read_split μ s 32 32

/-- Reading a window a word store misses. -/
theorem Mem.read_write_word_disjoint {M : Mem} (hwf : Mem.Wf M) (n : Nat) (v : B256) {a len : Nat}
    (h : n + 32 ≤ a ∨ a + len ≤ n) : ((M.write n v.toBytes).read a len).1 = (M.read a len).1 :=
  Mem.read_write_disjoint hwf n _ (by rw [B256.length_toBytes]; exact h)

/-- A read strictly inside a stored word, past its first byte. -/
theorem Mem.read_write_word_inside {M : Mem} (hwf : Mem.Wf M) (n : Nat) (v : B256) {a len : Nat}
    (h1 : n < a) (h2 : a + len ≤ n + 32) :
    ((M.write n v.toBytes).read a len).1 = v.toBytes.sliceD (a - n) len 0 := by
  rw [((Mem.reads_data M).write hwf n _).read]
  exact Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega)

/-! ## Keeping memory off a set of windows -/

/-- Byte `i` lies outside every half-open window `[lo, hi)` of `W`. -/
def Mem.OffWindows (W : List (Nat × Nat)) (i : Nat) : Prop :=
  ∀ w ∈ W, i < w.1 ∨ w.2 ≤ i

/-- `M'` is at least as large as `M` and reads as `M` at every byte off the windows `W`. -/
def Mem.KeepsOff (M M' : Mem) (W : List (Nat × Nat)) : Prop :=
  M.size ≤ M'.size ∧ ∀ i, Mem.OffWindows W i → M'.data.getD i 0 = M.data.getD i 0

theorem Mem.KeepsOff.refl (M : Mem) (W : List (Nat × Nat)) : Mem.KeepsOff M M W :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Mem.KeepsOff.trans {M M' M'' : Mem} {W : List (Nat × Nat)}
    (h1 : Mem.KeepsOff M M' W) (h2 : Mem.KeepsOff M' M'' W) : Mem.KeepsOff M M'' W :=
  ⟨le_trans h1.1 h2.1, fun i hi => (h2.2 i hi).trans (h1.2 i hi)⟩

/-- Keeping off fewer windows keeps off more. -/
theorem Mem.KeepsOff.mono {M M' : Mem} {W W' : List (Nat × Nat)} (h : Mem.KeepsOff M M' W)
    (hsub : W ⊆ W') : Mem.KeepsOff M M' W' :=
  ⟨h.1, fun i hi => h.2 i fun w hw => hi w (hsub hw)⟩

/-- Agreement outside one window, on a well-formed memory whose growth reads as zero, is keeping
off that window. -/
theorem Mem.KeepsOff.of_agreeOutside {M M' : Mem} {lo hi : Nat} (h : Mem.AgreeOutside M M' lo hi)
    (hwf : Mem.Wf M) (hzero : ∀ i, M.size ≤ i → (i < lo ∨ hi ≤ i) → M'.data.getD i 0 = 0) :
    Mem.KeepsOff M M' [(lo, hi)] := by
  refine ⟨h.1, fun i hi' => ?_⟩
  have hout := hi' (lo, hi) List.mem_cons_self
  by_cases hlt : i < M.size
  · exact h.2 i hlt hout
  · rw [hzero i (by omega) hout]
    have hsz : M.data.size ≤ i := le_trans hwf (by omega)
    simp only [Array.getD, show ¬ i < M.data.size from by omega, ↓reduceDIte]

/-- **B3.**  A byte image of `M` gives one of `M'` agreeing with it off the windows. -/
theorem Mem.Reads.keepsOff {M M' : Mem} {img : Bytes} {W : List (Nat × Nat)}
    (hr : Mem.Reads M img) (hk : Mem.KeepsOff M M' W) :
    ∃ img' : Bytes, Mem.Reads M' img' ∧ ∀ i, Mem.OffWindows W i → img'.getD i 0 = img.getD i 0 :=
  ⟨M'.data.toList, Mem.reads_data M', fun i hi => by
    rw [← Mem.reads_data M' i, hk.2 i hi, hr i]⟩

/-- A word all of whose bytes lie off the windows reads the same after keeping off them. -/
theorem memWord_keepsOff {M M' : Mem} {W : List (Nat × Nat)} (hk : Mem.KeepsOff M M' W)
    {o : Nat} (hoff : ∀ j, j < 32 → Mem.OffWindows W (o + j)) : memWord M' o = memWord M o :=
  memWord_congr fun j hj => hk.2 _ (hoff j hj)

/-- Carried words off the windows survive. -/
theorem Words.keepsOff {M M' : Mem} {W : List (Nat × Nat)} {L : List (Nat × B256)}
    (h : Words M L) (hk : Mem.KeepsOff M M' W)
    (hoff : ∀ o v, (o, v) ∈ L → ∀ j, j < 32 → Mem.OffWindows W (o + j)) : Words M' L := by
  intro o v hm
  obtain ⟨hs, hv⟩ := h o v hm
  exact ⟨le_trans hs hk.1, (memWord_keepsOff hk (hoff o v hm)).trans hv⟩

/-- Recorded map words off the windows survive. -/
theorem MemMatches.keepsOff {ρ : B256} {mem : MemMap} {M M' : Mem} {W : List (Nat × Nat)}
    (h : MemMatches ρ mem M) (hk : Mem.KeepsOff M M' W)
    (hoff : ∀ o v, (o, v) ∈ mem → ∀ j, j < 32 → Mem.OffWindows W (o + j)) :
    MemMatches ρ mem M' := by
  intro o v hm
  obtain ⟨hs, hv⟩ := h o v hm
  exact ⟨le_trans hs hk.1, by rw [memWord_keepsOff hk (hoff o v hm)]; exact hv⟩

end Blanc.Lift
