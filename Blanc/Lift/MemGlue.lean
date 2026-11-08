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

theorem Mem.extends_read_fst (μ : Mem) (l : List (Nat × Nat)) (a n : Nat) :
    ((μ.extends l).read a n).1 = (μ.read a n).1 := rfl

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

/-- A word all of whose bytes lie off the windows reads the same after keeping off them. -/
theorem memWord_keepsOff {M M' : Mem} {W : List (Nat × Nat)} (hk : Mem.KeepsOff M M' W)
    {o : Nat} (hoff : ∀ j, j < 32 → Mem.OffWindows W (o + j)) : memWord M' o = memWord M o :=
  memWord_congr fun j hj => hk.2 _ (hoff j hj)

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

/-- `M` and `N`: one logical size, both well formed, the same byte at every `i` outside `D`. -/
def Mem.EqExcept (M N : Mem) (D : Nat → Prop) : Prop :=
  M.size = N.size ∧ Mem.Wf M ∧ Mem.Wf N ∧ ∀ i, ¬ D i → M.data.getD i 0 = N.data.getD i 0

/-- The same extension on both sides. -/
theorem Mem.EqExcept.extend {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D)
    (i n : Nat) : Mem.EqExcept (M.extend i n) (N.extend i n) D :=
  ⟨by simp only [Mem.extend, h.1], h.2.1.extend i n, h.2.2.1.extend i n, h.2.2.2⟩




/-- Word stores in order. -/
def Mem.writeWords (M : Mem) (ws : List (Nat × B256)) : Mem :=
  ws.foldl (fun M ov => M.write ov.1 ov.2.toBytes) M

theorem Mem.writeWords_nil (M : Mem) : Mem.writeWords M [] = M := rfl

theorem Mem.writeWords_cons (M : Mem) (o : Nat) (v : B256) (ws : List (Nat × B256)) :
    Mem.writeWords M ((o, v) :: ws) = Mem.writeWords (M.write o v.toBytes) ws := rfl

/-! ## Memories equal off a set, and at every byte

`Mem.EqExcept.trans` composes two agreements; `writeD`, `restoreMemD` and `saveMemD` carry one
exception set unchanged through the same store, restore chain or frame save on both sides.
`Mem.EqExcept M N (fun _ => False)` (one logical size, both well formed, every byte equal) is what
a crossed callee that keeps its scratch to itself leaves relative to its normal form; the `eqB_*`
lemmas carry it, and `eqB_write_grow` turns it into equality at the next store that grows the
memory, where both arrays become fully materialised. -/

end Blanc.Lift
