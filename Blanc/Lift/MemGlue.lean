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


/-! ## Literal memory from bytes and sizes

`Mem.Reads`, `Mem.Wf` and the logical size do not determine a memory: the materialised array
may stop short of the logical size.  The lemmas below recover full `Mem` equality.
`Mem.EqExcept M N D` is agreement at every byte outside `D`, at one logical size, both well
formed; the same writes (or `restoreMem` chains) shrink `D` by the windows they cover.
`Mem.Full` (the array materialised to the logical size) holds after a growing write and is kept
by every write, so two fully materialised memories that agree everywhere are equal. -/

/-- Equal logical size, equal materialised length and equal bytes give equal memories. -/
theorem Mem.eq_of_size_dataSize_getD {M N : Mem} (logical : M.size = N.size)
    (physical : M.data.size = N.data.size) (bytes : ∀ i, M.data.getD i 0 = N.data.getD i 0) :
    M = N := by
  cases M with
  | mk dM sM =>
  cases N with
  | mk dN sN =>
  simp only at logical physical bytes
  subst logical
  congr 1
  apply Array.ext physical
  intro i h1 h2
  have e := bytes i
  simp only [Array.getD, h1, h2, ↓reduceDIte, Array.getInternal_eq_getElem] at e
  exact e

/-- A write's logical size depends only on the logical size it starts from. -/
theorem Mem.size_write_eq (μ : Mem) (n : Nat) (xs : Bytes) :
    (μ.write n xs).size =
      if xs = [] then μ.size else if n + xs.length ≤ μ.size then μ.size else ceil32 (n + xs.length) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    simp only [Mem.write, reduceCtorEq, ↓reduceIte]
    split_ifs <;> rfl

/-- A write's bytes: the payload over the window, the old bytes elsewhere. -/
theorem Mem.write_getD {μ : Mem} (hwf : Mem.Wf μ) (n : Nat) (xs : Bytes) (i : Nat) :
    (μ.write n xs).data.getD i 0 =
      if n ≤ i ∧ i < n + xs.length then xs.getD (i - n) 0 else μ.data.getD i 0 := by
  rw [(Mem.reads_data μ).write hwf n xs i, Bytes.getD_writeAt, ← Mem.reads_data μ i]

/-- The array materialised to the logical size. -/
def Mem.Full (μ : Mem) : Prop := μ.data.size = μ.size

/-- Every write keeps a memory fully materialised. -/
theorem Mem.Full.write {μ : Mem} (h : Mem.Full μ) (n : Nat) (xs : Bytes) :
    Mem.Full (μ.write n xs) := by
  cases xs with
  | nil => exact h
  | cons y ys =>
    unfold Mem.Full at h ⊢
    simp only [Mem.write]
    split_ifs with h1 h2
    · simp only [Array.size_writeD]; exact h
    · omega
    · simp only [Array.size_writeD, Array.size_copyD, Array.size_replicate]

/-- A write past the logical size materialises the whole array. -/
theorem Mem.full_write_of_grow {μ : Mem} {n : Nat} {xs : Bytes} (hne : xs ≠ [])
    (h : μ.size < n + xs.length) : Mem.Full (μ.write n xs) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons y ys =>
    unfold Mem.Full
    simp only [Mem.write, show ¬ n + (y :: ys).length ≤ μ.size from by omega, ↓reduceIte,
      Array.size_writeD, Array.size_copyD, Array.size_replicate]

/-- `M` and `N`: one logical size, both well formed, the same byte at every `i` outside `D`. -/
def Mem.EqExcept (M N : Mem) (D : Nat → Prop) : Prop :=
  M.size = N.size ∧ Mem.Wf M ∧ Mem.Wf N ∧ ∀ i, ¬ D i → M.data.getD i 0 = N.data.getD i 0

theorem Mem.EqExcept.refl {M : Mem} (hwf : Mem.Wf M) (D : Nat → Prop) : Mem.EqExcept M M D :=
  ⟨rfl, hwf, hwf, fun _ _ => rfl⟩

theorem Mem.EqExcept.symm {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D) :
    Mem.EqExcept N M D :=
  ⟨h.1.symm, h.2.2.1, h.2.1, fun i hi => (h.2.2.2 i hi).symm⟩

theorem Mem.EqExcept.mono {M N : Mem} {D D' : Nat → Prop} (h : Mem.EqExcept M N D)
    (hsub : ∀ i, D i → D' i) : Mem.EqExcept M N D' :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi => h.2.2.2 i fun hd => hi (hsub i hd)⟩

/-- A callee that keeps off windows and keeps the size leaves a memory equal off them. -/
theorem Mem.KeepsOff.eqExcept {M M' : Mem} {W : List (Nat × Nat)} (h : Mem.KeepsOff M M' W)
    (hsz : M'.size = M.size) (hwf : Mem.Wf M) (hwf' : Mem.Wf M') :
    Mem.EqExcept M M' (fun i => ¬ Mem.OffWindows W i) :=
  ⟨hsz.symm, hwf, hwf', fun i hi => (h.2 i (not_not.mp hi)).symm⟩

/-- The same write on both sides covers its window. -/
theorem Mem.EqExcept.write {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D)
    (n : Nat) (xs : Bytes) :
    Mem.EqExcept (M.write n xs) (N.write n xs) (fun i => D i ∧ ¬ (n ≤ i ∧ i < n + xs.length)) := by
  refine ⟨by rw [Mem.size_write_eq, Mem.size_write_eq, h.1], h.2.1.write n xs,
    h.2.2.1.write n xs, fun i hi => ?_⟩
  rw [Mem.write_getD h.2.1, Mem.write_getD h.2.2.1]
  split_ifs with hw
  · rfl
  · exact h.2.2.2 i fun hd => hi ⟨hd, hw⟩

/-- The same extension on both sides. -/
theorem Mem.EqExcept.extend {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D)
    (i n : Nat) : Mem.EqExcept (M.extend i n) (N.extend i n) D :=
  ⟨by simp only [Mem.extend, h.1], h.2.1.extend i n, h.2.2.1.extend i n, h.2.2.2⟩

/-- No exception left, both fully materialised: equal. -/
theorem Mem.EqExcept.eq {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D)
    (hD : ∀ i, ¬ D i) (hM : Mem.Full M) (hN : Mem.Full N) : M = N :=
  Mem.eq_of_size_dataSize_getD h.1 (by rw [hM, hN, h.1]) fun i => h.2.2.2 i (hD i)

/-- The same restore chain on both sides covers the counter word and every restored word. -/
theorem Mem.EqExcept.restoreMem (c : Nat) :
    ∀ {M N : Mem} {D : Nat → Prop} {p : Nat} (ws : List B256), Mem.EqExcept M N D →
      Mem.EqExcept (_root_.Blanc.Lift.restoreMem c M p ws) (_root_.Blanc.Lift.restoreMem c N p ws)
        (fun i => D i ∧ (ws ≠ [] → ¬ (c ≤ i ∧ i < c + 32)) ∧
          ∀ j, j < ws.length → ¬ (p - 32 * j ≤ i ∧ i < p - 32 * j + 32))
  | M, N, D, p, [], h => h.mono fun i hi => ⟨hi, fun h => absurd rfl h, fun j hj => absurd hj
      (Nat.not_lt_zero _)⟩
  | M, N, D, p, w :: ws, h => by
    have h2 := ((h.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes).restoreMem c
      (p := p - 32) ws
    rw [B256.length_toBytes, B256.length_toBytes] at h2
    refine h2.mono fun i hi => ⟨hi.1.1.1, fun _ => hi.1.2, fun j hj => ?_⟩
    simp only [List.length_cons] at hj
    rcases j with _ | j
    · simpa only [Nat.mul_zero, Nat.sub_zero] using hi.1.1.2
    · rw [show p - 32 * (j + 1) = p - 32 - 32 * j by omega]
      exact hi.2.2 j (by omega)

/-- `restoreMem` keeps a memory fully materialised. -/
theorem Mem.Full.restoreMem (c : Nat) :
    ∀ {M : Mem} {p : Nat} (ws : List B256), Mem.Full M →
      Mem.Full (_root_.Blanc.Lift.restoreMem c M p ws)
  | _, _, [], h => h
  | _, p, _ :: ws, h => Mem.Full.restoreMem c ws ((h.write p _).write c _)

end Blanc.Lift
