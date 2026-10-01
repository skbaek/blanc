import Blanc.Lift.PackedSha

/-!
# `sha256(abi.encodePacked(a, b))` of two words, size-optimised constants

The same solc 0.6 site as `Blanc/Lift/PackedSha.lean` (pack, word-copy loop, merge, precompile
call), as solc emits it where its constant optimiser favours code size (creation code, where
the optimiser's run count is 1): the word-copy loop's `-32` is `PUSH1 0x1f NOT` instead of a
`PUSH32`, and the merge's all-ones mask is `PUSH1 0 NOT`.  Each costs one `NOT` (3 gas) more
than the `PUSH32` form, so a copy pass is 82 gas, the merge 124, the whole call site from the
copy loop 607 and the site with the packing 736 (plus memory expansion).

The packing (`pack2Tree`) and the call (`shaCallTree`) are shared with `PackedSha`.  The
statements mirror `mcpy_iter`, `mcpy_exit`, `merge0`, `copy_sha_gen`, `copy_sha` and
`packed_sha_pair` with the size-optimised trees.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The size-optimised shapes -/

/-- The copy body with `-32` as `PUSH1 0x1f NOT`, ending in the back-edge `JUMP` to entry `k`. -/
def mcpyBodyN (r0 r1 : UInt8) (k : Nat) : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg .mload) (.next (.reg (.dup 2)) (.next (.reg .mstore)
    (.next (.push [0x1f] (by decide)) (.next (.reg .not) (.next (.reg (.swap 0))
      (.next (.reg (.swap 2)) (.next (.reg .add) (.next (.reg (.swap 1))
        (.next (.push [0x20] (by decide)) (.next (.reg (.swap 1)) (.next (.reg (.dup 2))
          (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .add)
            (.next (.push [r0, r1] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.jump k)))))))))))))))))

/-- The copy loop head: the `len < 32` test, the size-optimised body on failure, `exit`
otherwise. -/
def mcpyTreeN (e0 e1 r0 r1 : UInt8) (k : Nat) (exit : SFunc) : SFunc :=
  .dest (.next (.push [0x20] (by decide)) (.next (.reg (.dup 3)) (.next (.reg .lt)
    (.next (.push [e0, e1] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.branch (mcpyBodyN r0 r1 k) exit)))))

/-- The partial-word merge with the all-ones mask as `PUSH1 0 NOT`, then `K`. -/
def mergeTreeN (K : SFunc) : SFunc :=
  .dest (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg .mload)
    (.next (.push [0x20] (by decide)) (.next (.reg (.swap 3)) (.next (.reg (.dup 4))
      (.next (.reg .sub) (.next (.push [0x01, 0x00] (by decide)) (.next (.reg .exp)
        (.next (.push [0x00] (by decide)) (.next (.reg .not) (.next (.reg .add)
          (.next (.reg (.dup 0)) (.next (.reg .not) (.next (.reg (.swap 0)) (.next (.reg (.swap 2))
            (.next (.reg .and) (.next (.reg (.swap 1)) (.next (.reg .and) (.next (.reg .or)
              (.next (.reg (.swap 0)) (.next (.reg .mstore) K))))))))))))))))))))))

theorem not_1f : (~~~ Bytes.toB256 [0x1f]) = Bytes.toB256 minus32Push := by decide +kernel

theorem not0_add_zero : (~~~ Bytes.toB256 [0x00]) + 0 = B256.max := by decide +kernel

/-! ## The copy loop -/

section Copy

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}

/-- **One copy pass** (`len ≥ 32`) from the head through the back-edge goto into entry `k`:
82 gas and the destination word's expansion. -/
theorem mcpyN_iter {s d l n n' : Nat} (hl : 32 ≤ l) (hl' : l < 2 ^ 256) (hs : M.size = n)
    (hn' : max n (d + 32) = n')
    (hn : n % 32 = 0) (hsrc : s + 32 ≤ n) (hd : d % 32 = 0) (hsl : s + 64 < 2 ^ 256)
    (hdl : d + 64 < 2 ^ 256) (hR : R.length < 1000)
    (hk : fs[k]? = some T) (hkC : k ∉ C)
    (kont : SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 (s + 32) :: Nat.toB256 (d + 32) :: Nat.toB256 (l - 32) :: R)
        (M.write d (M.read s 32).1) G) T r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M
        (G + (79 + (3 + (calculateMemoryGasCost n' - calculateMemoryGasCost n)))))
      (mcpyTreeN e0 e1 r0 r1 k X) r := by
  subst hn'
  rw [show G + (79 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)))
    = G + 47 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)) + 32
    by omega]
  unfold mcpyTreeN mcpyBodyN
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt (v := 0) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 hl' (by norm_num)]
    simp only [show ¬l < 32 by omega, ↓reduceIte]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_zero ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Bytes.toB256 (M.read s 32).1) ?_
    (by rw [toNat_toB256' (by omega)]) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs hn hsrc
  · rw [toNat_toB256' (by omega)]; exact read_covered hs hn hsrc
  refine rxc_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (M' := M.write d (M.read s 32).1) ?_ ?_ ?_
  · rw [toNat_toB256' (by omega)]; exact charge_word hs hn hd
  · rw [toNat_toB256' (by omega), toBytes_read]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_not not_1f (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_add' (add_minus32 hl hl') (by simp only [List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_push rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons]; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons]; omega) ?_
  refine rxc_add' (push20_add (by omega)) (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons]; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_add' (push20_add (by omega)) (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons]; omega) ?_
  exact rxc_jump hk hkC kont

/-- **The copy's exit test** (`len < 32`): 23 gas, then `X`. -/
theorem mcpyN_exit {s d l : Nat} (hl : l < 32) (hR : R.length < 1000)
    (kont : SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M G) X r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M (G + 23))
      (mcpyTreeN e0 e1 r0 r1 k X) r := by
  unfold mcpyTreeN
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt (v := 1) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by norm_num)]
    simp only [hl, ↓reduceIte]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  exact rxc_branch_succ (by decide) kont

/-- **The merge with nothing left over**: the destination word is read (extending memory by
the word at `d`) and stored back.  124 gas and the expansion. -/
theorem mergeN0 {s d n n' : Nat} {K : SFunc} (hs : M.size = n) (hn : n % 32 = 0)
    (hn' : max n (d + 32) = n')
    (hsrc : s + 32 ≤ n) (hd : d % 32 = 0) (hsl : s < 2 ^ 256) (hdl : d < 2 ^ 256)
    (hR : R.length < 1000)
    (kont : SFunc.RunExactCut fs sevm C
      (St b (Bytes.toB256 [0x20] :: R) ((M.read d 32).2.write d (M.read d 32).1) G) K r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 0 :: R) M
        (G + (121 + (3 + (calculateMemoryGasCost n' - calculateMemoryGasCost n)))))
      (mergeTreeN K) r := by
  subst hn'
  rw [show G + (121 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)))
    = G + 114 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)) + 7
    by omega]
  have hs' : (M.read d 32).2.size = max n (d + 32) := read_ext_size hs hn hd
  unfold mergeTreeN
  refine rxc_dest ?_
  refine rxc_mload (c := 3) (v := Bytes.toB256 (M.read s 32).1) ?_
    (by rw [toNat_toB256' hsl]) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [toNat_toB256' hsl]; exact charge_covered hs hn hsrc
  · rw [toNat_toB256' hsl]; exact read_covered hs hn hsrc
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload_ext (v := Bytes.toB256 (M.read d 32).1) (M' := (M.read d 32).2) ?_
    (by rw [toNat_toB256' hdl]) (by rw [toNat_toB256' hdl]) (by simp only [List.length_cons]; omega) ?_
  · rw [toNat_toB256' hdl]; exact charge_word hs hn hd
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_dup (n := 4) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_sub' (v := Nat.toB256 32) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_exp' (c := 60) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_not rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_add' (v := B256.max) (by rw [bexp_256_32]; exact not0_add_zero) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_not (v := 0) B256.not_max (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_and (b256_and_zero _) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_and (b256_max_and _) (by simp only [List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_or (b256_or_zero _) (by simp only [List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_mstore (M' := (M.read d 32).2.write d (M.read d 32).1) ?_ ?_ kont
  · rw [toNat_toB256' hdl]; exact charge_covered hs' (by omega) (by omega)
  · rw [toNat_toB256' hdl, toBytes_read]

end Copy

/-! ## The whole site -/

section Site

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 c0 c1 v0 v1 : UInt8} {k : Nat}
  {fail1 fail2 T : SFunc}

/-- **Copy, merge and call over memory of any size** `n ≥ d`: 607 gas and the expansion to
`max n (d + 0x60)`; the result image is `shaImg img d w1 w2`.  The starting tree's exit `X` is
arbitrary (a first pass inlined in the caller's tree jumps to the loop entry `k`). -/
theorem copy_shaN_gen {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256} {X : SFunc}
    (hk : fs[k]? = some (mcpyTreeN e0 e1 r0 r1 k
      (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : d + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 246 < 2 ^ 256) :
    ∃ b' M', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg img d w1 w2) ∧ M'.size = max n (d + 96) ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M
          (G + (607 + (calculateMemoryGasCost (max n (d + 96)) - calculateMemoryGasCost n))))
        (mcpyTreeN e0 e1 r0 r1 k X) r := by
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
    hnodeleg hwarm hpre hfork hdepth (by omega) (by simp only [List.length_cons]; omega) (by omega)
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
  rw [show G + (607 + (calculateMemoryGasCost n3 - calculateMemoryGasCost n)) =
    G + 62 + 184 + 50
      + (121 + (3 + (calculateMemoryGasCost n3 - calculateMemoryGasCost n2))) + 23
      + (79 + (3 + (calculateMemoryGasCost n2 - calculateMemoryGasCost n1)))
      + (79 + (3 + (calculateMemoryGasCost n1 - calculateMemoryGasCost n))) by omega]
  -- the copy: two passes and the exit test
  refine mcpyN_iter (s := s) (d := d) (l := 64) (n := n) (n' := n1)
    (by omega) (by omega) hs (by omega) hn (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.length_cons]; omega) hk hkC ?_
  refine mcpyN_iter (s := s + 32) (d := d + 32) (l := 32) (n := n1) (n' := n2)
    (by omega) (by omega) hs5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.length_cons]; omega) hk hkC ?_
  refine mcpyN_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) (by simp only [List.length_cons]; omega) ?_
  refine mergeN0 (s := s + 64) (d := d + 64) (n := n2) (n' := n3) hs6 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [List.length_cons]; omega) ?_
  -- the call
  unfold shaCallTree
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr7 64 hw7) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs7 (by omega) (by omega)
  · rw [h40]; exact read_covered hs7 (by omega) (by omega)
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_add' (add_toB256' (c := d + 64) (by omega) (by omega)) (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 64) (by omega) (by omega) (by omega)) (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_dup (n := 5) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_gas (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine .next hstep ?_
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
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
  refine rxc_returndatasize (by simp only [List.length_cons]; omega) ?_
  rw [hrd]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  exact kont


/-- **Copy, merge and call**: from the copy loop's head with two words `w1`, `w2` at `s` and
`s + 0x20` to be copied to the free pointer `d = s + 0x40`, the two passes (the first inlined,
the second through entry `k`), the exit test, the merge, and the precompile call over the
copied 64 bytes with its checks: `copy_shaN_gen` when memory ends by `d + 0x20`.  607 gas and
the expansion to `d + 0x60`.  The stack under the
copy's operands carries the length `0x40`, three words the tail discards around the free pointer `d`, and the
precompile's address.  The successor world is `ShaCallPost`-related, and the continuation `T` starts with
the returned size and `d` on the stack. -/
theorem copy_shaN {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    (hk : fs[k]? = some (mcpyTreeN e0 e1 r0 r1 k
      (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
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
          (G + (607 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost n))))
        (mcpyTreeN e0 e1 r0 r1 k (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))) r := by
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ := copy_shaN_gen (X := mergeTreeN
    (shaCallTree c0 c1 v0 v1 fail1 fail2 T)) (x1 := x1) (x3 := x3) (x4 := x4) (R := R) (G := G)
    hk hkC hwf hr hs hn hdn hsd hd32 hd96 hdb hfp hw1 hw2 hR hnodeleg hwarm hpre hfork hdepth hG
  have hmax : max n (d + 96) = d + 96 := by omega
  refine ⟨b', M', shaImg img d w1 w2, hpost, hwf', hr', by rw [hs', hmax],
    (shaImg_out (d := d) (start := 64) (len := 32) (by omega)).trans hfp, shaImg_digest, fun r kont => ?_⟩
  have hc := hrun r kont
  rwa [hmax] at hc

/-- **`sha256(abi.encodePacked(a, b))`** with `b` on top of `a` (and the precompile's address
`2` below them), the free pointer at `f` (word-aligned, past the scratch words) and memory of
size `n ≤ f + 0x60`: the packing, then `copy_shaN` from `f + 0x20` to `f + 0x60`.  736 gas and
the expansion to `f + 0xc0`. -/
theorem packed_sha_pairN {img : Bytes} {n f : Nat} {a bw : B256}
    (hk : fs[k]? = some (mcpyTreeN e0 e1 r0 r1 k
      (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
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
          (G + (736 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n))))
        (pack2Tree (mcpyTreeN e0 e1 r0 r1 k (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
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
    copy_shaN (fs := fs) (sevm := sevm) (C := C) (b := b) (R := R) (M := M4) (G := G)
      (T := T) (fail1 := fail1) (fail2 := fail2) (n := f + 96) (s := f + 32) (d := f + 96)
      (x1 := Nat.toB256 (f + 32)) (x3 := Nat.toB256 (f + 96))
      (x4 := Nat.toB256 f)
      hk hkC hwf4 hr4 hs4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (packImg_word64 hf96) (packImg_a hf96) (packImg_b hf96) hR hnodeleg hwarm hpre
      hfork hdepth hG
  refine ⟨b', M', img', hpost, hwf', hr', by omega, hw', hh', fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show G + (736 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n)) =
    G + (607 + (calculateMemoryGasCost (f + 96 + 96) - calculateMemoryGasCost (f + 96))) + 90
      + (3 + (calculateMemoryGasCost (f + 96) - calculateMemoryGasCost s1)) + 12
      + (3 + (calculateMemoryGasCost s1 - calculateMemoryGasCost n)) + 21 by
    rw [show f + 96 + 96 = f + 192 by omega]; omega]
  unfold pack2Tree
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp only [List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs hn (by omega)
  · rw [h40]; exact read_covered hs hn (by omega)
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (M' := M1) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs hn (by omega)]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add' (push20_add' (a := f + 32) (c := f + 64) rfl (by omega)) (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (M' := M2) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs1 (by omega) (by omega),
      show max s1 (f + 64 + 32) = f + 96 by omega]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add' (push20_add' (a := f + 64) (c := f + 96) rfl (by omega)) (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_
    (by rw [h40]; exact read_word hr2 64 hfp2) ?_ (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by omega) (by omega)
  · rw [h40]; exact read_covered hs2 (by omega) (by omega)
  refine rxc_push rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 96) (by omega) (by omega) (by omega)) (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs2 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by omega) (by omega)
  refine rxc_push rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 (f + 96)) ?_
    (by rw [h40]; exact read_word hr4 64 (packImg_word64 hf96)) ?_ (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs4 (by omega) (by omega)
  · rw [h40]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by omega)]; exact read_word hr4 f (packImg_len hf96)) ?_
    (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs4 (by omega) (by omega)
  · rw [toNat_toB256' (by omega)]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  exact hc

end Site

end Blanc.Lift
