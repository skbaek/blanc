import Blanc.Lift.BeaconDeposit.BodyEventKit
import Blanc.Lift.BeaconDeposit.CountView

/-!
# Body segment 2, the two one-word copy loops

The amount (`t_0630_c7`, loop entry 26, clean-up `t_065c_c26`, 263 gas) and the index
(`t_06d7_c3`, loop entry 11, clean-up `t_0703_c11`, 263 gas): solc's copy loop copies the one
word holding the eight little-endian bytes to the tail, exits at once, and the clean-up keeps the
word's top eight bytes (`maskTop8`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The copied word `V` at `d`, then its top eight bytes. -/
def memB (M : Mem) (d : Nat) (V : B256) : Mem :=
  (M.write d V.toBytes).write d (maskTop8 &&& V).toBytes

/-- Its image. -/
def imgB (X : Bytes) (d : Nat) (V : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt X d V.toBytes) d (maskTop8 &&& V).toBytes

theorem RW.memB {M : Mem} {X : Bytes} (h : RW M X) (d : Nat) (V : B256) :
    RW (memB M d V) (imgB X d V) :=
  (h.write _ _).write _ _

theorem ev_amount {sevm : Sevm} {b : Devm} {R : List B256} {G : Nat} {M : Mem} {X : Bytes}
    {o : Outcome} (hR : R.length ≤ 30) (h0 : RW M X) (hs : M.size = 608)
    (k : SFunc.RunExact prog sevm
      (St b (8 :: 640 :: R) (memB M 608 (Bytes.toB256 (X.sliceD 160 32 0))) G) t_0675_c3 o) :
    SFunc.RunExact prog sevm
      (St b (0 :: 160 :: 608 :: 8 :: 8 :: 160 :: 608 :: R) M (G + 263)) t_0630_c7 o := by
  have hs1 : (M.write 608 (Bytes.toB256 (X.sliceD 160 32 0)).toBytes).size = 640 :=
    sz_step hs (by decide) (B256.length_toBytes _) (by decide)
  have h1 := h0.write 608 (Bytes.toB256 (X.sliceD 160 32 0)).toBytes
  unfold t_0630_c7
  refine rx_dest ?_
  refine rx_dup (n := 3) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_zero ?_
  unfold t_0639_c7
  refine rx_dup (n := 1) (w := 160) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 160) (v := Bytes.toB256 (X.sliceD 160 32 0)) h0 hs (by decide) (by decide)
    (by decide) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 608) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 608) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 608) (c := 6) hs (by decide) (by decide) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_jump (j := 26) rfl ?_
  unfold t_0630_c26
  refine rx_dest ?_
  refine rx_dup (n := 3) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0648_c26
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := 160 :: 8 :: 608 :: R) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := 608 :: 8 :: R) rfl ?_
  refine rx_dup (n := 1) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 616) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 8 :: 616 :: R) rfl ?_
  refine rx_push (w := 31) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 8) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branchTo_zero ?_
  unfold t_065c_c26
  refine rx_dup (n := 0) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 616) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 608) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 608) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 608) (v := Bytes.toB256 (X.sliceD 160 32 0)) h1 hs1 (by decide)
    (by decide) (by decide) (Bytes.readWord_writeAt_self _ _ _) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 24) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_exp' (c := 60) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_sub (by simp only [List.length_cons]; omega) ?_
  refine rx_not (v := maskTop8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 608) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 608) (c := 3) hs1 (by decide) (by decide) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 640) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 1) (S' := 616 :: 8 :: 640 :: R) rfl ?_
  refine rx_pop ?_
  exact k

theorem ev_index {sevm : Sevm} {b : Devm} {R : List B256} {G : Nat} {M : Mem} {X : Bytes}
    {o : Outcome} (hR : R.length ≤ 30) (h0 : RW M X) (hs : M.size = 800)
    (k : SFunc.RunExact prog sevm
      (St b (8 :: 832 :: R) (memB M 800 (Bytes.toB256 (X.sliceD 224 32 0))) G) t_071c_c4 o) :
    SFunc.RunExact prog sevm
      (St b (0 :: 224 :: 800 :: 8 :: 8 :: 224 :: 800 :: R) M (G + 263)) t_06d7_c3 o := by
  have hs1 : (M.write 800 (Bytes.toB256 (X.sliceD 224 32 0)).toBytes).size = 832 :=
    sz_step hs (by decide) (B256.length_toBytes _) (by decide)
  have h1 := h0.write 800 (Bytes.toB256 (X.sliceD 224 32 0)).toBytes
  unfold t_06d7_c3
  refine rx_dest ?_
  refine rx_dup (n := 3) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_zero ?_
  unfold t_06e0_c3
  refine rx_dup (n := 1) (w := 224) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 224) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 224) (v := Bytes.toB256 (X.sliceD 224 32 0)) h0 hs (by decide) (by decide)
    (by decide) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 800) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 800) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 800) (c := 6) hs (by decide) (by decide) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_jump (j := 11) rfl ?_
  unfold t_06d7_c11
  refine rx_dest ?_
  refine rx_dup (n := 3) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_06ef_c11
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := 224 :: 8 :: 800 :: R) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := 800 :: 8 :: R) rfl ?_
  refine rx_dup (n := 1) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 808) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) (S' := 8 :: 808 :: R) rfl ?_
  refine rx_push (w := 31) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 8) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branchTo_zero ?_
  unfold t_0703_c11
  refine rx_dup (n := 0) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 2) (w := 808) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 800) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) (w := 800) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mload (inat := 800) (v := Bytes.toB256 (X.sliceD 224 32 0)) h1 hs1 (by decide)
    (by decide) (by decide) (Bytes.readWord_writeAt_self _ _ _) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 24) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_exp' (c := 60) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_sub (by simp only [List.length_cons]; omega) ?_
  refine rx_not (v := maskTop8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) (w := 800) rfl (by simp only [List.length_cons]; omega) ?_
  refine ex_mstore (inat := 800) (c := 3) hs1 (by decide) (by decide) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 832) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 1) (S' := 808 :: 8 :: 832 :: R) rfl ?_
  refine rx_pop ?_
  exact k

end Blanc.Lift.BeaconDeposit
