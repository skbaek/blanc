import Blanc.Lift.PackedSha

/-!
# The solc packed-SHA site over memory of any size

`copy_sha` (`Blanc/Lift/PackedSha.lean`) walks the copy loop, the merge and the precompile call
of a solc 0.6 `sha256(abi.encodePacked(...))` site when memory ends within a word of the copy's
destination (the free pointer).  Inside a larger function the packed buffer is often written
*below* the memory's end (earlier `abi.encode` buffers extended it): `copy_sha_gen` is the same
site over memory of any word-aligned size `n ≥ d`, charging the expansion to
`max n (d + 0x60)`, with the result image named (`shaImg`) so that callers can carry facts
about the rest of memory.  The starting tree's exit is arbitrary (the first pass is inlined in
the caller's tree and jumps to the loop entry `k`).

Also: the cut walk step for `CALLDATACOPY` and a byte-window frame rule.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The image after the site: the two words copied to `d` and the digest written over the
first. -/
def shaImg (img : Bytes) (d : Nat) (w1 w2 : B256) : Bytes :=
  Bytes.writeAt (copyImg2 img d w1 w2) d (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes

/-- A byte window disjoint from a write reads as before. -/
theorem sliceD_writeAt_out {bs xs : Bytes} {start len n : Nat}
    (h : start + len ≤ n ∨ n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 = bs.sliceD start len 0 := by
  rcases h with h | h
  · exact Bytes.sliceD_writeAt_before _ _ _ _ _ h
  · exact Bytes.sliceD_writeAt_after _ _ _ _ _ h

theorem shaImg_out {img : Bytes} {d start len : Nat} {w1 w2 : B256}
    (h : start + len ≤ d ∨ d + 64 ≤ start) :
    (shaImg img d w1 w2).sliceD start len 0 = img.sliceD start len 0 := by
  unfold shaImg copyImg2
  rw [sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]

theorem shaImg_digest {img : Bytes} {d : Nat} {w1 w2 : B256} :
    (shaImg img d w1 w2).sliceD d 32 0 = (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes := by
  unfold shaImg
  have := Bytes.sliceD_writeAt (copyImg2 img d w1 w2)
    (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes d
  rwa [B256.length_toBytes] at this

section CutCopy

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- `CALLDATACOPY` inside a cut run. -/
theorem rxc_calldatacopy {di si sz : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + (St b (di :: si :: sz :: S) M (G + c)).extCost [⟨di.toNat, sz.toNat⟩] = c)
    (hw : M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M')
    (k : SFunc.RunExactCut fs sevm C (St b S M' G) f r) :
    SFunc.RunExactCut fs sevm C (St b (di :: si :: sz :: S) M (G + c))
      (.next (.reg .calldatacopy) f) r :=
  .next (Ninst.runCompiled_calldatacopy_of (devm := St b (di :: si :: sz :: S) M (G + c))
    (G := G) rfl hc hw rfl) k

end CutCopy

section Site

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 c0 c1 v0 v1 : UInt8} {k : Nat}
  {fail1 fail2 T X : SFunc}

/-- **Copy, merge and call over memory of any size** `n ≥ d` (`copy_sha` without the premise
that memory ends by `d + 0x20`): 598 gas and the expansion to `max n (d + 0x60)`; the result
image is `shaImg img d w1 w2`. -/
theorem copy_sha_gen {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : n + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 256 < 2 ^ 256) :
    ∃ b' M', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg img d w1 w2) ∧ M'.size = max n (d + 96) ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M
          (G + (598 + (calculateMemoryGasCost (max n (d + 96)) - calculateMemoryGasCost n))))
        (mcpyTree e0 e1 r0 r1 k X) r := by
  set n1 := max n (d + 32) with hn1
  set n2 := max n (d + 64) with hn2
  set n3 := max n (d + 96) with hn3
  have m3 := calculateMemoryGasCost_mono (show n ≤ n1 by omega)
  have m4 := calculateMemoryGasCost_mono (show n1 ≤ n2 by omega)
  have m5 := calculateMemoryGasCost_mono (show n2 ≤ n3 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hw1' : (M.read s 32).1 = w1.toBytes := by rw [hr.read, hw1]
  set M5 := M.write d (M.read s 32).1 with hM5
  have hwf5 : Mem.Wf M5 := hwf.write _ _
  have hr5 : Mem.Reads M5 (Bytes.writeAt img d w1.toBytes) := by
    rw [hM5, hw1']; exact hr.write hwf _ _
  have hs5 : M5.size = n1 := by
    rw [hM5, hw1', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hw2' : (M5.read (s + 32) 32).1 = w2.toBytes := by
    rw [hr5.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw2]
  set M6 := M5.write (d + 32) (M5.read (s + 32) 32).1 with hM6
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg2 img d w1 w2) := by
    rw [hM6, hw2']; exact hr5.write hwf5 _ _
  have hs6 : M6.size = n2 := by
    rw [hM6, hw2', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  set M7 := (M6.read (d + 64) 32).2.write (d + 64) (M6.read (d + 64) 32).1 with hM7
  have hs6' : (M6.read (d + 64) 32).2.size = n3 := by
    rw [read_ext_size hs6 (by omega) (by omega)]; omega
  have hwf7 : Mem.Wf M7 := (hwf6.extend _ _).write _ _
  have hr7 : Mem.Reads M7 (copyImg2 img d w1 w2) := by
    rw [hM7, hr6.read]
    exact Mem.Reads.write_self (hwf6.extend _ _) (hr6.extend _ _) _
  have hs7 : M7.size = n3 := by
    rw [hM7, ← toBytes_read, Mem.size_write_word_aligned (by omega) (by omega), hs6']; omega
  have hin : (M7.read d 64).1 = w1.toBytes ++ w2.toBytes := by
    rw [hr7.read, copyImg2_input]
  have hF : (Nat.toB256 d).toNat = d := toNat_toB256' (by omega)
  obtain ⟨b', hpost, hstep⟩ := staticcall_sha_step (sevm := sevm) (b := b)
    (iiw := Nat.toB256 d) (oiw := Nat.toB256 d) (S := Nat.toB256 (d + 64) :: 2 :: R)
    (M := M7) (G := G + 62)
    (by rw [hF, hs7]; exact memExtsSize_two_covered (by omega) (by omega) (by omega))
    hnodeleg hwarm hpre hfork hdepth (by omega) (by simp; omega) (by omega)
  rw [hF, hin] at hpost hstep
  set M8 := M7.write d (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes with hM8
  have hwf8 : Mem.Wf M8 := hwf7.write _ _
  have hr8 : Mem.Reads M8 (shaImg img d w1 w2) := hr7.write hwf7 d _
  have hs8 : M8.size = n3 := by
    rw [hM8, Mem.size_write_word_aligned (by omega) (by omega), hs7]; omega
  have hw7 : (copyImg2 img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [copyImg2_word64 (by omega), hfp]
  have hw8 : (shaImg img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [shaImg_out (by omega), hfp]
  have hrd : b'.returnData.length.toB256 = Nat.toB256 32 := by
    rw [hpost.returnData, B256.length_toBytes]
  refine ⟨b', M8, hpost, hwf8, hr8, hs8, fun r kont => ?_⟩
  rw [show G + (598 + (calculateMemoryGasCost n3 - calculateMemoryGasCost n)) =
    G + 62 + 184 + 50
      + (118 + (3 + (calculateMemoryGasCost n3 - calculateMemoryGasCost n2))) + 23
      + (76 + (3 + (calculateMemoryGasCost n2 - calculateMemoryGasCost n1)))
      + (76 + (3 + (calculateMemoryGasCost n1 - calculateMemoryGasCost n))) by omega]
  -- the copy: two passes and the exit test
  refine mcpy_iter (s := s) (d := d) (l := 64) (n := n) (n' := n1)
    (by omega) (by omega) hs (by omega) hn (by omega) (by omega) (by omega) (by omega)
    (by simp; omega) hk hkC ?_
  refine mcpy_iter (s := s + 32) (d := d + 32) (l := 32) (n := n1) (n' := n2)
    (by omega) (by omega) hs5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp; omega) hk hkC ?_
  refine mcpy_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) (by simp; omega) ?_
  refine merge0 (s := s + 64) (d := d + 64) (n := n2) (n' := n3) hs6 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by simp; omega) ?_
  -- the call
  unfold shaCallTree
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr7 64 hw7) ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs7 (by omega) (by omega)
  · rw [h40]; exact read_covered hs7 (by omega) (by omega)
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_add' (add_toB256' (c := d + 64) (by omega) (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 64) (by omega) (by omega) (by omega)) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 5) rfl (by simp; omega) ?_
  refine rxc_gas (by simp; omega) ?_
  refine .next hstep ?_
  refine rxc_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr8 64 hw8) ?_ (by omega) ?_
  · rw [h40]; exact charge_covered hs8 (by omega) (by omega)
  · rw [h40]; exact read_covered hs8 (by omega) (by omega)
  refine rxc_returndatasize (by simp; omega) ?_
  rw [hrd]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  exact kont

end Site

end Blanc.Lift
