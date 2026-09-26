import Blanc.Lift.ExactWalkCut

/-!
# The solc word-copy loop

solc 0.6 copies a `bytes` payload into an ABI encoding with one fixed loop
(`abi_encode` of `bytes memory`, and the event and `sha256` argument encoders):

```
head:  JUMPDEST DUP4 DUP2 LT ISZERO PUSH2 exit JUMPI
body:  DUP2 DUP2 ADD MLOAD DUP4 DUP3 ADD MSTORE PUSH1 0x20 ADD PUSH2 head JUMP
```

over the stack `i :: src :: dst :: len :: R`, copying `mload(src + i)` to
`dst + i` for `i = 0, 32, …` while `i < len`.  `copyLoopTree` is that shape as a
lifted tree (entry `k` is the head; the push immediates are parameters, since
they are the code's own addresses), and `copy_loop` is its gas-exact run built
with `SFunc.RunExactCut.iterate`: `N` iterations from any starting count `j0`,
the memory image after them (`copyImg`: the source words laid over the
destination), its size (`copySize`) and the exact gas (`copyGas`, `67` per
iteration and `26` for the exit test, plus the destination's memory expansion
as a difference of `calculateMemoryGasCost`).

`copy_step` (one iteration, ending at the cut head) also serves a first pass
that solc inlines before the loop entry, as the beacon deposit contract's
`get_deposit_count` wrapper does; `copy_exit` is the failing test.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Memory arithmetic -/

theorem ceilDiv32_mono {a b : Nat} (h : a ≤ b) : ceilDiv a 32 ≤ ceilDiv b 32 := by
  unfold ceilDiv; split_ifs <;> omega

theorem calculateMemoryGasCost_mono {a b : Nat} (h : a ≤ b) :
    calculateMemoryGasCost a ≤ calculateMemoryGasCost b := by
  unfold calculateMemoryGasCost
  have h1 := ceilDiv32_mono h
  have h2 : ceilDiv a 32 ^ 2 ≤ ceilDiv b 32 ^ 2 := Nat.pow_le_pow_left h1 2
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.div_le_div_right h2)

theorem ceil32_of_mod {x : Nat} (h : x % 32 = 0) : ceil32 x = x := by
  unfold ceil32; rw [h]

/-- A word window at an aligned offset over an aligned image extends it to
the window's end, or not at all. -/
theorem memExtSize_word_aligned {m i : Nat} (hm : m % 32 = 0) (hi : i % 32 = 0) :
    memExtSize m i 32 = max m (i + 32) := by
  unfold memExtSize
  rw [ite_eq_right (by decide)]
  unfold ceilDiv
  rw [ite_eq_left hm, ite_eq_left (by omega)]
  omega

theorem Mem.size_write_word_aligned {μ : Mem} {i : Nat} {w : B256} (hm : μ.size % 32 = 0)
    (hi : i % 32 = 0) : (μ.write i w.toBytes).size = max μ.size (i + 32) := by
  rw [Mem.size_write_word_at]
  split_ifs with h
  · omega
  · rw [ceil32_of_mod (by omega)]; omega

/-! ## Byte-image algebra -/

theorem Bytes.length_writeAt' (bs : Bytes) (n : Nat) (xs : Bytes) :
    (Bytes.writeAt bs n xs).length = max bs.length (n + xs.length) := by
  simp only [Bytes.writeAt, List.length_append, List.takeD_length, List.length_drop]
  omega

theorem List.ext_getD' {α : Type} {l l' : List α} (d : α) (hlen : l.length = l'.length)
    (h : ∀ i, l.getD i d = l'.getD i d) : l = l' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i
  simpa [List.getD, h1, h2] using this

/-- Two adjacent writes are one write of the concatenation. -/
theorem Bytes.writeAt_writeAt_append (bs : Bytes) (n : Nat) (xs ys : Bytes) :
    Bytes.writeAt (Bytes.writeAt bs n xs) (n + xs.length) ys = Bytes.writeAt bs n (xs ++ ys) := by
  apply List.ext_getD' 0
  · simp only [Bytes.length_writeAt', List.length_append]; omega
  · intro i
    simp only [Bytes.getD_writeAt, List.length_append]
    by_cases h1 : n + xs.length ≤ i ∧ i < n + xs.length + ys.length
    · rw [ite_eq_left h1, ite_eq_left (by omega), Blanc.List.getD_append_right 0 (by omega)]
      congr 1; omega
    · rw [ite_eq_right h1]
      by_cases h2 : n ≤ i ∧ i < n + xs.length
      · rw [ite_eq_left h2, ite_eq_left (by omega), Blanc.List.getD_append_left 0 (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- An empty write changes no byte a reader sees. -/
theorem _root_.Blanc.Mem.Reads.writeAt_nil {μ : Mem} {bs : Bytes} (h : Mem.Reads μ bs) (n : Nat) :
    Mem.Reads μ (Bytes.writeAt bs n []) := by
  intro i
  rw [h i, Bytes.getD_writeAt, ite_eq_right (by simp)]

/-! ## The loop's shape -/

/-- The copy body, ending in the back-edge `JUMP` to the head at entry `k`. -/
def copyBody (r0 r1 : UInt8) (k : Nat) : SFunc :=
  .next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg .mload)
    (.next (.reg (.dup 3)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .mstore)
      (.next (.push [0x20] (by decide)) (.next (.reg .add)
        (.next (.push [r0, r1] (by simp)) (.jump k)))))))))))

/-- The copy loop head: the `i < len` test, the body on success, `exit` otherwise. -/
def copyLoopTree (e0 e1 r0 r1 : UInt8) (k : Nat) (exit : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 3)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.reg .iszero)
    (.next (.push [e0, e1] (by simp)) (.branch (copyBody r0 r1 k) exit))))))

/-! ## The loop's state -/

/-- The image after `j` iterations: the first `j` source words laid over the
destination. -/
def copyImg (img : Bytes) (src dst j : Nat) : Bytes :=
  Bytes.writeAt img dst (img.sliceD src (32 * j) 0)

/-- The memory size after `j` iterations. -/
def copySize (n dst j : Nat) : Nat := max n (dst + 32 * j)

/-- The stack at the head of iteration `j`. -/
def copyStack (srcB dstB lenB : B256) (R : List B256) (j : Nat) : List B256 :=
  (32 * j).toB256 :: srcB :: dstB :: lenB :: R

/-- The gas from the head of iteration `j` to the exit tree, of `N` in all. -/
def copyGas (n dst N j : Nat) : Nat :=
  67 * (N - j) + 26 +
    (calculateMemoryGasCost (copySize n dst N) - calculateMemoryGasCost (copySize n dst j))

/-- What a copy of `N` words from `srcB` to `dstB` over an image of size `n`
needs: `N` is the iteration count of `len`, the source lies inside the image,
source and destination do not overlap, nothing overflows a word, and the
destination and the image are word-aligned. -/
structure CopyWf (srcB dstB lenB : B256) (R : List B256) (n N : Nat) : Prop where
  iter : ∀ j, j < N ↔ 32 * j < lenB.toNat
  n32 : n % 32 = 0
  dst32 : dstB.toNat % 32 = 0
  src_le : srcB.toNat + 32 * N ≤ n
  disj : srcB.toNat + 32 * N ≤ dstB.toNat ∨ dstB.toNat + 32 * N ≤ srcB.toNat
  src_lt : srcB.toNat + 32 * N < 2 ^ 256
  dst_lt : dstB.toNat + 32 * N + 32 < 2 ^ 256
  room : R.length < 1000

section Copy

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {srcB dstB lenB : B256} {R : List B256}
  {img : Bytes} {n N : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {exitT : SFunc}

theorem copySize_mod (h : CopyWf srcB dstB lenB R n N) (j : Nat) :
    copySize n dstB.toNat j % 32 = 0 := by
  have := h.n32; have := h.dst32; unfold copySize; omega

theorem copyGas_mono (j j' : Nat) (hj : j ≤ j') :
    calculateMemoryGasCost (copySize n dstB.toNat j) ≤
      calculateMemoryGasCost (copySize n dstB.toNat j') :=
  calculateMemoryGasCost_mono (by unfold copySize; omega)

/-- **One iteration** (`j < N`), from the head to the cut back-edge: 67 gas and
the destination word's expansion. -/
theorem copy_step {C : List Nat} (hkC : k ∈ C) (h : CopyWf srcB dstB lenB R n N) {j : Nat}
    (hj : j < N) {M : Mem} (hwf : Mem.Wf M) (hr : Mem.Reads M (copyImg img srcB.toNat dstB.toNat j))
    (hs : M.size = copySize n dstB.toNat j) (G : Nat) :
    ∃ M', Mem.Wf M' ∧ Mem.Reads M' (copyImg img srcB.toNat dstB.toNat (j + 1)) ∧
      M'.size = copySize n dstB.toNat (j + 1) ∧
      SFunc.RunExactCut fs sevm C
        (St b (copyStack srcB dstB lenB R j) M
          (G + (67 + (calculateMemoryGasCost (copySize n dstB.toNat (j + 1))
            - calculateMemoryGasCost (copySize n dstB.toNat j)))))
        (copyLoopTree e0 e1 r0 r1 k exitT)
        (.at k (St b (copyStack srcB dstB lenB R (j + 1)) M' G)) := by
  have hroom := h.room
  have hsl := h.src_lt; have hdl := h.dst_lt; have hsle := h.src_le; have hdis := h.disj
  have hn32 := h.n32; have hd32 := h.dst32
  have hi : ((32 * j).toB256).toNat = 32 * j := B256.toNat_toB256_of_lt (by omega)
  have hlt : B256.ltCheck (32 * j).toB256 lenB = 1 := by
    rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, hi]
    exact (h.iter j).1 hj
  have haddS : ((32 * j).toB256 + srcB).toNat = srcB.toNat + 32 * j := by
    rw [B256.toNat_add, hi, Nat.lo_eq_of_lt (by omega)]; omega
  have haddD : ((32 * j).toB256 + dstB).toNat = dstB.toNat + 32 * j := by
    rw [B256.toNat_add, hi, Nat.lo_eq_of_lt (by omega)]; omega
  have hnext : Bytes.toB256 [0x20] + (32 * j).toB256 = (32 * (j + 1)).toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, hi, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x20]).toNat = 32 from by decide, Nat.lo_eq_of_lt (by omega)]
    omega
  set s := srcB.toNat
  set d := dstB.toNat
  have hsz32 : M.size % 32 = 0 := by rw [hs]; exact copySize_mod h j
  have hread : (M.read (s + 32 * j) 32).1 = img.sliceD (s + 32 * j) 32 0 := by
    rw [hr.read, copyImg]
    rcases hdis with hd | hd
    · exact Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)
    · exact Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [List.length_sliceD]; omega)
  have hM : (M.read (s + 32 * j) 32).2 = M :=
    Mem.read_snd_eq_self (memExtSize_of_le hsz32 (by rw [hs]; unfold copySize; omega))
  set w := Bytes.toB256 (img.sliceD (s + 32 * j) 32 0)
  have hwb : w.toBytes = img.sliceD (s + 32 * j) 32 0 :=
    Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)
  refine ⟨M.write (d + 32 * j) w.toBytes, hwf.write _ _, ?_, ?_, ?_⟩
  · have := hr.write hwf (d + 32 * j) w.toBytes
    rw [copyImg, hwb] at this
    rw [hwb, copyImg, show 32 * (j + 1) = 32 * j + 32 by omega, List.sliceD_split,
      ← Bytes.writeAt_writeAt_append, List.length_sliceD]
    exact this
  · rw [Mem.size_write_word_aligned hsz32 (by omega), hs]; unfold copySize; omega
  have hext : calculateMemoryGasCost (memExtSize (copySize n d j) (d + 32 * j) 32)
      - calculateMemoryGasCost (copySize n d j) =
      calculateMemoryGasCost (copySize n d (j + 1)) - calculateMemoryGasCost (copySize n d j) := by
    rw [memExtSize_word_aligned (copySize_mod h j) (by omega)]
    congr 2; unfold copySize; omega
  rw [show G + (67 + (calculateMemoryGasCost (copySize n d (j + 1))
      - calculateMemoryGasCost (copySize n d j))) =
    (G + 17) + (3 + (calculateMemoryGasCost (copySize n d (j + 1))
      - calculateMemoryGasCost (copySize n d j))) + 47 by omega]
  unfold copyLoopTree copyBody copyStack
  refine rxc_dest ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt hlt (by simp; omega) ?_
  refine rxc_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_zero ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_add (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := w) ?_ ?_ ?_ (by simp; omega) ?_
  · rw [St.extCost_eq hs, haddS, memExtSize_of_le (copySize_mod h j) (by unfold copySize; omega)]
    exact congrArg (gVerylow + ·) (Nat.sub_self _)
  · rw [haddS, hread]
  · rw [haddS, hM]
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_add (by simp; omega) ?_
  refine rxc_mstore (M' := M.write (d + 32 * j) w.toBytes) ?_ (by rw [haddD]) ?_
  · rw [St.extCost_eq hs, haddD, hext]; rfl
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add (by simp; omega) ?_
  rw [hnext]
  refine rxc_push rfl (by simp; omega) ?_
  exact rxc_jumpCut hkC

/-- **The exit test** (`N` done): 26 gas, then the exit tree. -/
theorem copy_exit {C : List Nat} (h : CopyWf srcB dstB lenB R n N) {M : Mem} {G : Nat} {r : Seg}
    (kx : SFunc.RunExactCut fs sevm C (St b (copyStack srcB dstB lenB R N) M G) exitT r) :
    SFunc.RunExactCut fs sevm C (St b (copyStack srcB dstB lenB R N) M (G + 26))
      (copyLoopTree e0 e1 r0 r1 k exitT) r := by
  have hroom := h.room
  have hi : ((32 * N).toB256).toNat = 32 * N := B256.toNat_toB256_of_lt (by have := h.dst_lt; omega)
  have hlt : B256.ltCheck (32 * N).toB256 lenB = 0 := by
    rw [B256.ltCheck, ite_eq_right]
    rw [B256.lt_iff_toNat_lt_toNat, hi]
    exact fun hh => Nat.lt_irrefl N ((h.iter N).2 hh)
  unfold copyLoopTree
  unfold copyStack at kx ⊢
  refine rxc_dest ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt hlt (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  exact rxc_branch_succ (by decide) kx

/-- **The copy loop**, from the head of iteration `j0` through the exit tree, as
an exact cut run built with `SFunc.RunExactCut.iterate`: `copyGas` to the exit
tree, with the image, size and stack `copyImg`, `copySize` and `copyStack` at
`N`.  The exit continuation may end differently for each final memory (the
loop's memory is only known through its image), so the result is any `Rr`
that every exit establishes. -/
theorem copy_loop {C : List Nat} (hk : fs[k]? = some (copyLoopTree e0 e1 r0 r1 k exitT))
    (hkC : k ∉ C) (h : CopyWf srcB dstB lenB R n N) {j0 : Nat} (hj0 : j0 ≤ N)
    {M : Mem} (hwf : Mem.Wf M) (hr : Mem.Reads M (copyImg img srcB.toNat dstB.toNat j0))
    (hs : M.size = copySize n dstB.toNat j0) {Gx : Nat} (Rr : Seg → Prop)
    (hexit : ∀ M' : Mem, Mem.Wf M' → Mem.Reads M' (copyImg img srcB.toNat dstB.toNat N) →
      M'.size = copySize n dstB.toNat N →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) (St b (copyStack srcB dstB lenB R N) M' Gx) exitT r ∧
        (∀ d, r ≠ .at k d) ∧ Rr r) :
    ∃ r, SFunc.RunExactCut fs sevm C
      (St b (copyStack srcB dstB lenB R j0) M (Gx + copyGas n dstB.toNat N j0))
      (copyLoopTree e0 e1 r0 r1 k exitT) r ∧ Rr r := by
  let J : Nat → Devm → Prop := fun i devm => ∃ M', Mem.Wf M' ∧
    Mem.Reads M' (copyImg img srcB.toNat dstB.toNat (j0 + i)) ∧
    M'.size = copySize n dstB.toNat (j0 + i) ∧
    devm = St b (copyStack srcB dstB lenB R (j0 + i)) M' (Gx + copyGas n dstB.toNat N (j0 + i))
  exact SFunc.RunExactCut.iterate (fs := fs) (sevm := sevm) (C := C) hk hkC J (N - j0) Rr
    (fun i hi devm ⟨M', hwf', hr', hs', hdevm⟩ => by
      obtain ⟨M'', hwf'', hr'', hs'', hrun⟩ :=
        copy_step (fs := fs) (sevm := sevm) (b := b) (e0 := e0) (e1 := e1) (r0 := r0) (r1 := r1)
          (exitT := exitT) (List.mem_cons_self) h (j := j0 + i) (by omega) hwf' hr' hs'
          (Gx + copyGas n dstB.toNat N (j0 + i + 1))
      refine ⟨St b (copyStack srcB dstB lenB R (j0 + i + 1)) M''
        (Gx + copyGas n dstB.toNat N (j0 + i + 1)), ?_, M'', hwf'',
        by rwa [Nat.add_assoc] at hr'', by rwa [Nat.add_assoc] at hs'', by rw [Nat.add_assoc]⟩
      rw [hdevm]
      convert hrun using 2
      have m1 := copyGas_mono (n := n) (dstB := dstB) (j0 + i) (j0 + i + 1) (by omega)
      have m2 := copyGas_mono (n := n) (dstB := dstB) (j0 + i + 1) N (by omega)
      unfold copyGas
      omega)
    (fun devm ⟨M', hwf', hr', hs', hdevm⟩ => by
      have hN : j0 + (N - j0) = N := by omega
      rw [hN] at hr' hs' hdevm
      obtain ⟨r, hrun, hr0, hR⟩ := hexit M' hwf' hr' hs'
      refine ⟨r, ?_, hr0, hR⟩
      rw [hdevm, show Gx + copyGas n dstB.toNat N N = Gx + 26 by unfold copyGas; simp]
      exact copy_exit h hrun)
    (St b (copyStack srcB dstB lenB R j0) M (Gx + copyGas n dstB.toNat N j0))
    ⟨M, hwf, by simpa using hr, by simpa using hs, by simp⟩

end Copy

end Blanc.Lift
