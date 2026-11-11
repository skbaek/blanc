import Blanc.Lift.BeaconDeposit.BodyEventKit

/-!
# Body segment 2, third part: the signature and the index's length

From `0x0675` (tree `t_0675_c3`) to the index's copy loop (`t_06d7_c3`): the fourth head word,
the signature tail (length and `CALLDATACOPY` of 96 bytes, a zero word after it), the fifth head
word and the index's length.  207 gas.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The memory after the third part: six writes. -/
def memC (M : Mem) (sg : Bytes) : Mem :=
  (((((M.write 352 (384 : B256).toBytes).write 640 (96 : B256).toBytes).write 672 sg).write
    768 (0 : B256).toBytes).write 384 (512 : B256).toBytes).write 768 (8 : B256).toBytes

/-- Its image. -/
def imgC (X : Bytes) (sg : Bytes) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt X 352
    (384 : B256).toBytes) 640 (96 : B256).toBytes) 672 sg) 768 (0 : B256).toBytes) 384
    (512 : B256).toBytes) 768 (8 : B256).toBytes

theorem RW.memC {M : Mem} {X : Bytes} (h : RW M X) (sg : Bytes) : RW (memC M sg) (imgC X sg) :=
  ((((((h.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _)

theorem ev_sig {sevm : Sevm} {b : Devm} {sP wP pP : B256} {R : List B256} {G : Nat} {M : Mem}
    {X : Bytes} {o : Outcome} (hR : R.length ≤ 20) (h0 : RW M X) (hs : M.size = 640)
    (hc0 : X.sliceD 192 32 0 = (8 : B256).toBytes)
    (k : SFunc.RunExact prog sevm
      (St b (0 :: 224 :: 800 :: 8 :: 8 :: 224 :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 ::
        192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R)
        (memC M (sevm.data.sliceD sP.toNat 96 0)) G) t_06d7_c3 o) :
    SFunc.RunExact prog sevm
      (St b (8 :: 640 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 ::
        wP :: 48 :: pP :: R) M (G + 207)) t_0675_c3 o := by
  set M1 := M.write 352 (384 : B256).toBytes with hM1
  have hs1 : M1.size = 640 := sz_step hs (by decide) (B256.length_toBytes _) (by decide)
  have h1 : RW M1 _ := h0.write 352 (384 : B256).toBytes
  set M2 := M1.write 640 (96 : B256).toBytes with hM2
  have hs2 : M2.size = 672 := sz_step hs1 (by decide) (B256.length_toBytes _) (by decide)
  have h2 : RW M2 _ := h1.write 640 (96 : B256).toBytes
  set M3 := M2.write 672 (sevm.data.sliceD sP.toNat 96 0) with hM3
  have hs3 : M3.size = 768 := sz_step hs2 (by decide) (List.length_sliceD _ _ _ _) (by decide)
  have h3 : RW M3 _ := h2.write 672 (sevm.data.sliceD sP.toNat 96 0)
  set M4 := M3.write 768 (0 : B256).toBytes with hM4
  have hs4 : M4.size = 800 := sz_step hs3 (by decide) (B256.length_toBytes _) (by decide)
  have h4 : RW M4 _ := h3.write 768 (0 : B256).toBytes
  set M5 := M4.write 384 (512 : B256).toBytes with hM5
  have hs5 : M5.size = 800 := sz_step hs4 (by decide) (B256.length_toBytes _) (by decide)
  have h5 : RW M5 _ := h4.write 384 (512 : B256).toBytes
  set M6 := M5.write 768 (8 : B256).toBytes with hM6
  have hs6 : M6.size = 800 := sz_step hs5 (by decide) (B256.length_toBytes _) (by decide)
  have h6 : RW M6 _ := h5.write 768 (8 : B256).toBytes
  unfold t_0675_c3
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_dup (n := 6) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 640) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 384) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 352) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 352) (c := 3) hs (by decide) (by decide) ?_
  refine rx_dup (n := 8) (w := 96) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 640) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 640) (c := 6) hs1 (by decide) (by decide) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 672) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 9) (w := sP) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 9) (w := 96) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 96) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := sP) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) (w := 672) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_cdc (dn := 672) (zn := 96) (c := 22) hs2 (by decide) (by decide) (by decide) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 672) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 96) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 768) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 768 :: 0 :: 0 :: 96 :: sP :: 672 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine ex_mstore (inat := 768) (c := 6) hs3 (by decide) (by decide) ?_
  refine rx_push (w := 31) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 31 :: 96 :: sP :: 672 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 1) (S' := 96 :: 31 :: 0 :: sP :: 672 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_add' (v := 127) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 115792089237316195423570985008687907853269984665640564039457584007913129639904) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 96) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 96 :: sP :: 672 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 2) (S' := 672 :: 96 :: sP :: 0 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_add' (v := 768) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 8) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 768) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 512) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) (w := 384) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 384) (c := 3) hs4 (by decide) (by decide) ?_
  refine rx_dup (n := 9) (w := 192) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 192) (v := 8) h5 hs5 (by decide) (by decide) (by decide) (by peel; rw [hc0, B256.toB256_toBytes]) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 768) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 768) (c := 3) hs5 (by decide) (by decide) ?_
  refine rx_dup (n := 9) (w := 192) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 192) (v := 8) h6 hs6 (by decide) (by decide) (by decide) (by peel; rw [hc0, B256.toB256_toBytes]) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 1) (S' := 768 :: 8 :: 32 :: sP :: 0 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 2) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 800) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 3) (S' := 0 :: 8 :: 32 :: sP :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 1) (S' := 32 :: 8 :: 0 :: sP :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 11) (w := 192) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 224) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 2) (S' := sP :: 8 :: 0 :: 224 :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := 0 :: 8 :: 224 :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 1) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 8 :: 8 :: 224 :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 4) (w := 800) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 800 :: 8 :: 8 :: 224 :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 4) (w := 224) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 224 :: 800 :: 8 :: 8 :: 224 :: 800 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  exact k

end Blanc.Lift.BeaconDeposit
