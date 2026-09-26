import Blanc.Lift.PackedSha

/-!
# `copy_sha` and `packed_sha_pair` under the gas bound they use

`Blanc/Lift/PackedSha.lean` states `copy_sha` and `packed_sha_pair` with the premise
`G + 1000 < 2 ^ 256` on the gas left after the site, but the proofs use it only for the
precompile step (`staticcall_sha_step`, at `G + 62`), which needs `G + 246 < 2 ^ 256`.  A caller
whose own bound covers only the site's actual charge (the beacon deposit's dead insertion pass,
`G + deadGas h + sloadCost … < 2 ^ 256`) cannot discharge the stronger premise.  These are the
same two proofs, verbatim, under the premise they use.  (Weakening the premise in `PackedSha`
itself makes this module redundant; every existing caller passes `by omega`.)

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

section Site

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 c0 c1 v0 v1 : UInt8} {k : Nat}
  {fail1 fail2 T : SFunc}

/-- **Copy, merge and call** (`copy_sha` under `G + 246 < 2 ^ 256`): from the copy loop's head with two words `w1`, `w2` at `s` and
`s + 0x20` to be copied to the free pointer `d = s + 0x40`, the two passes (the first inlined,
the second through entry `k`), the exit test, the merge, and the precompile call over the
copied 64 bytes with its checks.  598 gas and the expansion to `d + 0x60`.  The stack under the
copy's operands carries the length `0x40`, three words the tail discards around the free pointer `d`, and the
precompile's address.  The successor world is `ShaCallPost`-related, and the continuation `T` starts with
the returned size and `d` on the stack. -/
theorem copy_sha_tight {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hnd : n ≤ d + 32) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : d + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 246 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' img' ∧ M'.size = d + 96 ∧
      img'.sliceD 64 32 0 = (Nat.toB256 d).toBytes ∧
      img'.sliceD d 32 0 = (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M
          (G + (598 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost n))))
        (mcpyTree e0 e1 r0 r1 k (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))) r := by
  have m3 := calculateMemoryGasCost_mono (show n ≤ d + 32 by omega)
  have m4 := calculateMemoryGasCost_mono (show d + 32 ≤ d + 64 by omega)
  have m5 := calculateMemoryGasCost_mono (show d + 64 ≤ d + 96 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hw1' : (M.read s 32).1 = w1.toBytes := by rw [hr.read, hw1]
  set M5 := M.write d (M.read s 32).1 with hM5
  have hwf5 : Mem.Wf M5 := hwf.write _ _
  have hr5 : Mem.Reads M5 (Bytes.writeAt img d w1.toBytes) := by
    rw [hM5, hw1']; exact hr.write hwf _ _
  have hs5 : M5.size = d + 32 := by
    rw [hM5, hw1', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hw2' : (M5.read (s + 32) 32).1 = w2.toBytes := by
    rw [hr5.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw2]
  set M6 := M5.write (d + 32) (M5.read (s + 32) 32).1 with hM6
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg2 img d w1 w2) := by
    rw [hM6, hw2']; exact hr5.write hwf5 _ _
  have hs6 : M6.size = d + 64 := by
    rw [hM6, hw2', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  set M7 := (M6.read (d + 64) 32).2.write (d + 64) (M6.read (d + 64) 32).1 with hM7
  have hs6' : (M6.read (d + 64) 32).2.size = d + 96 := by
    rw [read_ext_size hs6 (by omega) (by omega)]; omega
  have hwf7 : Mem.Wf M7 := (hwf6.extend _ _).write _ _
  have hr7 : Mem.Reads M7 (copyImg2 img d w1 w2) := by
    rw [hM7, hr6.read]
    exact Mem.Reads.write_self (hwf6.extend _ _) (hr6.extend _ _) _
  have hs7 : M7.size = d + 96 := by
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
  have hr8 := hr7.write hwf7 d (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes
  have hs8 : M8.size = d + 96 := by
    rw [hM8, Mem.size_write_word_aligned (by omega) (by omega), hs7]; omega
  have hw7 : (copyImg2 img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [copyImg2_word64 (by omega), hfp]
  have hw8 : (Bytes.writeAt (copyImg2 img d w1 w2) d
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes).sliceD 64 32 0 =
      (Nat.toB256 d).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw7]
  have hh8 : (Bytes.writeAt (copyImg2 img d w1 w2) d
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes).sliceD d 32 0 =
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes := by
    have := Bytes.sliceD_writeAt (copyImg2 img d w1 w2)
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes d
    rwa [B256.length_toBytes] at this
  have hrd : b'.returnData.length.toB256 = Nat.toB256 32 := by
    rw [hpost.returnData, B256.length_toBytes]
  refine ⟨b', M8, _, hpost, hwf8, hr8, hs8, hw8, hh8, fun r kont => ?_⟩
  rw [show G + (598 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost n)) =
    G + 62 + 184 + 50
      + (118 + (3 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost (d + 64)))) + 23
      + (76 + (3 + (calculateMemoryGasCost (d + 64) - calculateMemoryGasCost (d + 32))))
      + (76 + (3 + (calculateMemoryGasCost (d + 32) - calculateMemoryGasCost n))) by omega]
  -- the copy: two passes and the exit test
  refine mcpy_iter (s := s) (d := d) (l := 64) (n := n) (n' := d + 32)
    (by omega) (by omega) hs (by omega) hn (by omega) (by omega) (by omega) (by omega)
    (by simp; omega) hk hkC ?_
  refine mcpy_iter (s := s + 32) (d := d + 32) (l := 32) (n := d + 32) (n' := d + 64)
    (by omega) (by omega) hs5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp; omega) hk hkC ?_
  refine mcpy_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) (by simp; omega) ?_
  refine merge0 (s := s + 64) (d := d + 64) (n := d + 64) (n' := d + 96) hs6 (by omega)
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

/-- **`sha256(abi.encodePacked(a, b))`** (`packed_sha_pair` under `G + 246 < 2 ^ 256`) with `b` on top of `a` (and the precompile's address
`2` below them), the free pointer at `f` (word-aligned, past the scratch words) and memory of
size `n ≤ f + 0x60`: the packing, then `copy_sha` from `f + 0x20` to `f + 0x60`.  727 gas and
the expansion to `f + 0xc0`. -/
theorem packed_sha_pair_tight {img : Bytes} {n f : Nat} {a bw : B256}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (h96 : 96 ≤ n) (hnf : n ≤ f + 96) (hf32 : f % 32 = 0) (hf96 : 96 ≤ f)
    (hfb : f + 2000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 f).toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 246 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPost b b' (hashPairBytes a bw) ∧ Mem.Wf M' ∧
      Mem.Reads M' img' ∧ M'.size = f + 192 ∧
      img'.sliceD 64 32 0 = (Nat.toB256 (f + 96)).toBytes ∧
      img'.sliceD (f + 96) 32 0 = (Bytes.sha256 (a.toBytes ++ bw.toBytes)).toBytes ∧
      ∀ r, SFunc.RunExactCut fs sevm C
        (St b' (Nat.toB256 32 :: Nat.toB256 (f + 96) :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (bw :: a :: 2 :: R) M
          (G + (727 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n))))
        (pack2Tree (mcpyTree e0 e1 r0 r1 k (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
        r := by
  set s1 := max n (f + 64) with hs1_def
  have m1 := calculateMemoryGasCost_mono (show n ≤ s1 by omega)
  have m2 := calculateMemoryGasCost_mono (show s1 ≤ f + 96 by omega)
  have m3 := calculateMemoryGasCost_mono (show f + 96 ≤ f + 192 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  set M1 := M.write (f + 32) a.toBytes with hM1
  set M2 := M1.write (f + 64) bw.toBytes with hM2
  set M3 := M2.write f (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 (f + 96)).toBytes with hM4
  have hs1 : M1.size = s1 := by
    rw [hM1, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs2 : M2.size = f + 96 := by
    rw [hM2, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs3 : M3.size = f + 96 := by
    rw [hM3, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs4 : M4.size = f + 96 := by
    rw [hM4, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 := hr.write hwf (f + 32) a.toBytes
  have hr2 := hr1.write hwf1 (f + 64) bw.toBytes
  have hr3 := hr2.write hwf2 f (Nat.toB256 64).toBytes
  have hr4 : Mem.Reads M4 (packImg img f a bw) := hr3.write hwf3 64 _
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img (f + 32) a.toBytes) (f + 64)
      bw.toBytes).sliceD 64 32 0 = (Nat.toB256 f).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    copy_sha_tight (fs := fs) (sevm := sevm) (C := C) (b := b) (R := R) (M := M4) (G := G)
      (T := T) (fail1 := fail1) (fail2 := fail2) (n := f + 96) (s := f + 32) (d := f + 96)
      (x1 := Nat.toB256 (f + 32)) (x3 := Nat.toB256 (f + 96))
      (x4 := Nat.toB256 f)
      hk hkC hwf4 hr4 hs4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (packImg_word64 hf96) (packImg_a hf96) (packImg_b hf96) hR hnodeleg hwarm hpre
      hfork hdepth hG
  refine ⟨b', M', img', hpost, hwf', hr', by omega, hw', hh', fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show G + (727 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n)) =
    G + (598 + (calculateMemoryGasCost (f + 96 + 96) - calculateMemoryGasCost (f + 96))) + 90
      + (3 + (calculateMemoryGasCost (f + 96) - calculateMemoryGasCost s1)) + 12
      + (3 + (calculateMemoryGasCost s1 - calculateMemoryGasCost n)) + 21 by
    rw [show f + 96 + 96 = f + 192 by omega]; omega]
  unfold pack2Tree
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs hn (by omega)
  · rw [h40]; exact read_covered hs hn (by omega)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (M' := M1) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs hn (by omega)]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add' (a := f + 32) (c := f + 64) rfl (by omega)) (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (M' := M2) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs1 (by omega) (by omega),
      show max s1 (f + 64 + 32) = f + 96 by omega]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add' (a := f + 64) (c := f + 96) rfl (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_
    (by rw [h40]; exact read_word hr2 64 hfp2) ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by omega) (by omega)
  · rw [h40]; exact read_covered hs2 (by omega) (by omega)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 96) (by omega) (by omega) (by omega)) (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs2 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by omega) (by omega)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 (f + 96)) ?_
    (by rw [h40]; exact read_word hr4 64 (packImg_word64 hf96)) ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs4 (by omega) (by omega)
  · rw [h40]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by omega)]; exact read_word hr4 f (packImg_len hf96)) ?_
    (by simp; omega) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs4 (by omega) (by omega)
  · rw [toNat_toB256' (by omega)]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  exact hc

end Site

end Blanc.Lift
