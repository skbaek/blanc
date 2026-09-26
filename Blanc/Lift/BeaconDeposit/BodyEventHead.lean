import Blanc.Lift.BeaconDeposit.BodyEventKit

/-!
# Body segment 2, first part: the head words, the pubkey and the withdrawal credentials

From the return tag `0x0575` (tree `t_0575_c7`) to the amount's copy loop (`t_0630_c7`): the
five head words, the pubkey tail (`CALLDATACOPY` of 48 bytes and a zero word after it), the
withdrawal-credentials tail (32 bytes and a zero word), the third head word and the amount's
length.  371 gas.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The memory after the first part: ten writes. -/
def memA (M : Mem) (pk wc : Bytes) : Mem :=
  (((((((((M.write 256 (160 : B256).toBytes).write 416 (48 : B256).toBytes).write 448 pk).write
    496 (0 : B256).toBytes).write 288 (256 : B256).toBytes).write 512 (32 : B256).toBytes).write
    544 wc).write 576 (0 : B256).toBytes).write 320 (320 : B256).toBytes).write 576
    (8 : B256).toBytes

/-- Its image. -/
def imgA (X : Bytes) (pk wc : Bytes) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt X 256 (160 : B256).toBytes) 416
    (48 : B256).toBytes) 448 pk) 496 (0 : B256).toBytes) 288 (256 : B256).toBytes) 512
    (32 : B256).toBytes) 544 wc) 576 (0 : B256).toBytes) 320 (320 : B256).toBytes) 576
    (8 : B256).toBytes

theorem RW.memA {M : Mem} {X : Bytes} (h : RW M X) (pk wc : Bytes) :
    RW (memA M pk wc) (imgA X pk wc) :=
  ((((((((((h.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write _
    _).write _ _).write _ _)

theorem ev_head {sevm : Sevm} {b : Devm} {sP wP pP : B256} {R : List B256} {G : Nat} {M : Mem}
    {X : Bytes} {o : Outcome} (hR : R.length ≤ 20) (h0 : RW M X) (hs : M.size = 256)
    (hfp : X.sliceD 64 32 0 = (256 : B256).toBytes) (h80 : X.sliceD 128 32 0 = (8 : B256).toBytes)
    (k : SFunc.RunExact prog sevm
      (St b (0 :: 160 :: 608 :: 8 :: 8 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 ::
        192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R)
        (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) G) t_0630_c7 o) :
    SFunc.RunExact prog sevm
      (St b (192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) M (G + 371)) t_0575_c7 o := by
  set M1 := M.write 256 (160 : B256).toBytes with hM1
  have hs1 : M1.size = 288 := sz_step hs (by decide) (B256.length_toBytes _) (by decide)
  have h1 : RW M1 _ := h0.write 256 (160 : B256).toBytes
  set M2 := M1.write 416 (48 : B256).toBytes with hM2
  have hs2 : M2.size = 448 := sz_step hs1 (by decide) (B256.length_toBytes _) (by decide)
  have h2 : RW M2 _ := h1.write 416 (48 : B256).toBytes
  set M3 := M2.write 448 (sevm.data.sliceD pP.toNat 48 0) with hM3
  have hs3 : M3.size = 512 := sz_step hs2 (by decide) (List.length_sliceD _ _ _ _) (by decide)
  have h3 : RW M3 _ := h2.write 448 (sevm.data.sliceD pP.toNat 48 0)
  set M4 := M3.write 496 (0 : B256).toBytes with hM4
  have hs4 : M4.size = 544 := sz_step hs3 (by decide) (B256.length_toBytes _) (by decide)
  have h4 : RW M4 _ := h3.write 496 (0 : B256).toBytes
  set M5 := M4.write 288 (256 : B256).toBytes with hM5
  have hs5 : M5.size = 544 := sz_step hs4 (by decide) (B256.length_toBytes _) (by decide)
  have h5 : RW M5 _ := h4.write 288 (256 : B256).toBytes
  set M6 := M5.write 512 (32 : B256).toBytes with hM6
  have hs6 : M6.size = 544 := sz_step hs5 (by decide) (B256.length_toBytes _) (by decide)
  have h6 : RW M6 _ := h5.write 512 (32 : B256).toBytes
  set M7 := M6.write 544 (sevm.data.sliceD wP.toNat 32 0) with hM7
  have hs7 : M7.size = 576 := sz_step hs6 (by decide) (List.length_sliceD _ _ _ _) (by decide)
  have h7 : RW M7 _ := h6.write 544 (sevm.data.sliceD wP.toNat 32 0)
  set M8 := M7.write 576 (0 : B256).toBytes with hM8
  have hs8 : M8.size = 608 := sz_step hs7 (by decide) (B256.length_toBytes _) (by decide)
  have h8 : RW M8 _ := h7.write 576 (0 : B256).toBytes
  set M9 := M8.write 320 (320 : B256).toBytes with hM9
  have hs9 : M9.size = 608 := sz_step hs8 (by decide) (B256.length_toBytes _) (by decide)
  have h9 : RW M9 _ := h8.write 320 (320 : B256).toBytes
  set M10 := M9.write 576 (8 : B256).toBytes with hM10
  have hs10 : M10.size = 608 := sz_step hs9 (by decide) (B256.length_toBytes _) (by decide)
  have h10 : RW M10 _ := h9.write 576 (8 : B256).toBytes
  unfold t_0575_c7
  refine rx_dest ?_
  refine rx_push (w := 64) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 64) (v := 256) h0 hs (by decide) (by decide) (by decide) (by rw [hfp, B256.toB256_toBytes]) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 160) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 256) (c := 6) hs (by decide) (by decide) ?_
  refine rx_dup (n := 1) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 416) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 9) (w := 48) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 416 :: 48 :: 256 :: 64 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine ex_mstore (inat := 416) (c := 18) hs1 (by decide) (by decide) ?_
  refine rx_swap (n := 0) (S' := 64 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 1) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 64 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 288) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 64 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 2) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 320) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 96) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 352) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 128) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 384) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 192) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 5) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 448) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 14) (w := pP) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 14) (w := 48) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 48) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := pP) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) (w := 448) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_cdc (dn := 448) (zn := 48) (c := 15) hs2 (by decide) (by decide) (by decide) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 448) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 48) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 496) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 496) (c := 6) hs3 (by decide) (by decide) ?_
  refine rx_push (w := 31) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 79) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 115792089237316195423570985008687907853269984665640564039457584007913129639904) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 64) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := pP :: 64 :: 448 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 1) (S' := 448 :: 64 :: pP :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_add' (v := 512) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 7) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 512) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 256) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 6) (w := 288) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 288) (c := 3) hs4 (by decide) (by decide) ?_
  refine rx_dup (n := 12) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 512) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 512) (c := 3) hs5 (by decide) (by decide) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 544) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := pP :: 544 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 12) (w := wP) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 12) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := wP) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) (w := 544) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_cdc (dn := 544) (zn := 32) (c := 9) hs6 (by decide) (by decide) (by decide) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 544) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 576) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 576 :: 0 :: 0 :: 32 :: wP :: 544 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine ex_mstore (inat := 576) (c := 6) hs7 (by decide) (by decide) ?_
  refine rx_push (w := 31) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 31 :: 32 :: wP :: 544 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 1) (S' := 32 :: 31 :: 0 :: wP :: 544 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_add' (v := 63) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 115792089237316195423570985008687907853269984665640564039457584007913129639904) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 32 :: wP :: 544 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 2) (S' := 544 :: 32 :: wP :: 0 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_add' (v := 576) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 8) (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 576) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 320) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 6) (w := 320) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 320) (c := 3) hs8 (by decide) (by decide) ?_
  refine rx_dup (n := 12) (w := 128) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 128) (v := 8) h9 hs9 (by decide) (by decide) (by decide) (by peel; rw [h80, B256.toB256_toBytes]) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 576) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 576) (c := 3) hs9 (by decide) (by decide) ?_
  refine rx_dup (n := 12) (w := 128) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 128) (v := 8) h10 hs10 (by decide) (by decide) (by decide) (by peel; rw [h80, B256.toB256_toBytes]) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 1) (S' := 576 :: 8 :: 32 :: wP :: 0 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 2) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 608) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 3) (S' := 0 :: 8 :: 32 :: wP :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_swap (n := 1) (S' := 32 :: 8 :: 0 :: wP :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 14) (w := 128) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 2) (S' := wP :: 8 :: 0 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := 0 :: 8 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 1) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 8 :: 8 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 4) (w := 608) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 608 :: 8 :: 8 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  refine rx_dup (n := 4) (w := 160) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 0 :: 160 :: 608 :: 8 :: 8 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 :: 192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) rfl ?_
  exact k

end Blanc.Lift.BeaconDeposit
