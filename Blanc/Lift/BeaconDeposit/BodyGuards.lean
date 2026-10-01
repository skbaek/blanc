import Blanc.Lift.BeaconDeposit.BodySpec
import Jaune.MulDiv
import Blanc.Lift.ExactWalkCutOps

/-!
# Body segment 1: the six guards and the two `to_little_endian_64` calls

From the entry of `deposit` (entry 7, pc `0x0304`) to the return tag `0x0575` of the second
`to_little_endian_64` call (tree `t_0575_c7`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: guards
/-- **Segment 1 (`0x0304 → 0x0575`, trees `t_0304_c7 … t_0575_c7`).**  With the success path's
lengths `48, 32, 96` on the stack and a value passing the three value guards, the body runs its
six guards (each `JUMPI` jumps over its `Error(string)` revert block), calls
`to_little_endian_64(value / 1 gwei)` (allocating `0x80`), pushes the event topic and its
arguments, reads the count (`SLOAD 0x20`) and calls `to_little_endian_64(count)` (allocating
`0xc0`).  1882 gas and the count `SLOAD`.

Proof sketch.  The guards: `rx_*` steps with `rx_branch_succ` on each `JUMPI` (`EQ` of the
literal lengths, `LT`/`ISZERO` of `CALLVALUE` against `1 ether`, `MOD` by `1 gwei`, `GT`
against `2^64 - 1`; `MOD` needs a small `rx_mod` step alongside `rx_div`).  The calls:
`rx_callRet (j := 25)` with `to_little_endian_64_run` (`LittleEndian.lean`, over `mem0` then over
its `leImg`, 830 and 827 gas), exactly as `count_getter` does in `CountView.lean`; the `SLOAD`
with `Ninst.runCompiled_sload_selected` (it charges `sloadCost` and moves to `afterSload`).
The memory facts come from `leImg`'s `sliceD` algebra (`img1_fp`, `img1_len` in `CountView`). -/
theorem body_guards {sevm : Sevm} {b : Devm} {sel rt sP wP pP : B256} {G : Nat}
    (hcd : sevm.data.length < 2 ^ 256)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hv1 : 10 ^ 18 ≤ sevm.value.toNat)
    (hv2 : sevm.value.toNat % 10 ^ 9 = 0)
    (hv3 : sevm.value.toNat / 10 ^ 9 < 2 ^ 64) :
    ∃ b' M', Keep (afterSload sevm b solCountSlot) b' ∧
      BodyMem M' 256 0x100
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 (gweiAmount sevm).toNat),
          (0xc0, (8 : B256).toBytes),
          (0xe0, BeaconDeposit.le64 (b.getStorVal sevm.currentTarget solCountSlot).toNat)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80,
            gweiAmount sevm, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G) t_0575_c7 o →
        SFunc.RunExact prog sevm
          (St b [rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] mem0
            (G + (1882 + sloadCost sevm b solCountSlot))) t_0304_c7 o := by
  -- value-guard facts, bridging `.toNat` hypotheses to the `B256` operations the code runs
  have hyne : (1000000000 : B256) ≠ 0 := by decide
  have h1e9 : (1000000000 : B256).toNat = 10 ^ 9 := by decide
  have h1ether : (0x0de0b6b3a7640000 : B256).toNat = 10 ^ 18 := by decide
  have hmaskNat : (0xffffffffffffffff : B256).toNat = 2 ^ 64 - 1 := by decide
  have hnotlt1 : ¬ sevm.value < (0x0de0b6b3a7640000 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, h1ether]; omega
  have hltz : B256.ltCheck sevm.value (0x0de0b6b3a7640000 : B256) = 0 := by
    rw [B256.ltCheck, if_neg hnotlt1]
  have hmodv : sevm.value % (1000000000 : B256) = 0 := by
    apply B256.toNat_inj
    rw [B256.toNat_mod hyne, h1e9, hv2]
    rfl
  have hgweiNat : (gweiAmount sevm).toNat = sevm.value.toNat / 10 ^ 9 := by
    rw [gweiAmount, B256.toNat_div hyne, h1e9]
  have hle64 : gweiAmount sevm ≤ (0xffffffffffffffff : B256) := by
    rw [B256.le_iff_toNat_le_toNat, hgweiNat, hmaskNat]; omega
  have hgtz : B256.gtCheck (gweiAmount sevm) (0xffffffffffffffff : B256) = 0 := by
    rw [B256.gtCheck, if_neg (B256.not_lt.mpr hle64)]
  set cnt := b.getStorVal sevm.currentTarget solCountSlot with hcntdef
  set b'' := afterSload sevm b solCountSlot with hb''def
  -- the first `to_little_endian_64` call, over `mem0`, encoding the gwei amount
  obtain ⟨M1, hwf1, hr1, hs1, hcall1⟩ := to_little_endian_64_run (sevm := sevm) (b := b)
      (G := G + (874 + sloadCost sevm b solCountSlot)) (v := gweiAmount sevm)
      (ret := (1344 : B256))
      (rest := [96, gweiAmount sevm, rt, 96, sP, 32, wP, 48, pP, 440, sel])
      (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) wf_mem0 reads_mem0 (by rw [mem0_size]) (by rw [mem0_size])
      img0_fp (by rw [p80]) (by rw [p80]; omega) (by rw [p80]; decide) hcd
  have himg1 : Mem.Reads M1 (img1 (gweiAmount sevm)) := hr1
  have hs1' : M1.size = 192 := by rw [hs1, mem0_size, p80]; decide
  have hfp2 : Bytes.toB256 ((img1 (gweiAmount sevm)).sliceD 64 32 0) = (192 : B256) := by
    rw [img1_fp, B256.toB256_toBytes]; decide
  -- the second `to_little_endian_64` call, over the first call's image, encoding the count
  obtain ⟨M', hwf', hr', hs', hcall2⟩ := to_little_endian_64_run (sevm := sevm) (b := b'')
      (G := G) (v := cnt) (ret := (1397 : B256))
      (rest := [96, sP, (128 : B256), 32, wP, 48, pP, BeaconDeposit.depositEventTopic,
        (128 : B256), gweiAmount sevm, rt, 96, sP, 32, wP, 48, pP, 440, sel])
      (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) hwf1 himg1 (by rw [hs1']) (by rw [hs1']; decide) hfp2
      (by decide) (by decide) (by decide) hcd
  set img2 := leImg (img1 (gweiAmount sevm)) (192 : B256) cnt with himg2def
  have himg2_eq : img2 = Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (img1 (gweiAmount sevm)) 192 (8 : B256).toBytes) 64
        (256 : B256).toBytes)
      224 (BeaconDeposit.le64 cnt.toNat) := by
    rw [himg2def, leImg, show (192 : B256).toNat = 192 from by decide,
      show (192 : B256) + 64 = (256 : B256) from by decide]
  have hs'' : M'.size = 256 := by
    rw [hs', hs1', show (192 : B256).toNat = 192 from by decide]; decide
  have himg2_fp : img2.sliceD 64 32 0 = (256 : B256).toBytes := by
    rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    have := Bytes.sliceD_writeAt
      (Bytes.writeAt (img1 (gweiAmount sevm)) 192 (8 : B256).toBytes) (256 : B256).toBytes 64
    rwa [B256.length_toBytes] at this
  have himg1_160 : (img1 (gweiAmount sevm)).sliceD 160 8 0 =
      BeaconDeposit.le64 (gweiAmount sevm).toNat := by
    rw [img1, leImg, p80, show (128 + 32 : Nat) = 160 by rfl]
    have h8 : (BeaconDeposit.le64 (gweiAmount sevm).toNat).length = 8 := rfl
    have := Bytes.sliceD_writeAt
      (Bytes.writeAt (Bytes.writeAt img0 128 (8 : B256).toBytes) 64
        (Bytes.toB256 [0x80] + 64).toBytes)
      (BeaconDeposit.le64 (gweiAmount sevm).toNat) 160
    rwa [h8] at this
  have himg2_128 : img2.sliceD 128 32 0 = (8 : B256).toBytes := by
    rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact img1_len (gweiAmount sevm)
  have himg2_160 : img2.sliceD 160 8 0 = BeaconDeposit.le64 (gweiAmount sevm).toNat := by
    rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact himg1_160
  have himg2_192 : img2.sliceD 192 32 0 = (8 : B256).toBytes := by
    rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by decide)]
    exact Bytes.sliceD_writeAt _ _ _
  have himg2_224 : img2.sliceD 224 8 0 = BeaconDeposit.le64 cnt.toNat := by
    rw [himg2_eq]
    have h8 : (BeaconDeposit.le64 cnt.toNat).length = 8 := rfl
    have := Bytes.sliceD_writeAt
      (Bytes.writeAt (Bytes.writeAt (img1 (gweiAmount sevm)) 192 (8 : B256).toBytes) 64
        (256 : B256).toBytes)
      (BeaconDeposit.le64 cnt.toNat) 224
    rwa [h8] at this
  have hBodyMem : BodyMem M' 256 256
      [(128, (8 : B256).toBytes), (160, BeaconDeposit.le64 (gweiAmount sevm).toNat),
        (192, (8 : B256).toBytes), (224, BeaconDeposit.le64 cnt.toNat)] := by
    refine ⟨hwf', hs'', img2, hr', himg2_fp, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact himg2_128
    · exact himg2_160
    · exact himg2_192
    · exact himg2_224
  have hg1 : leGas mem0.size (Bytes.toB256 [0x80]).toNat = 830 := by
    rw [mem0_size, p80]; decide
  have hg2 : leGas M1.size (192 : B256).toNat = 827 := by
    rw [hs1']; decide
  have h80 : Bytes.toB256 [0x80] = (128 : B256) := by decide
  rw [hg1, h80] at hcall1
  rw [hg2] at hcall2
  refine ⟨b'', M', Keep.refl b'', hBodyMem, fun o k => ?_⟩
  rw [show G + (1882 + sloadCost sevm b solCountSlot) =
    (((G + (874 + sloadCost sevm b solCountSlot)) + 830) + 8) + 170 by omega]
  unfold t_0304_c7
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup (n := 6) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_eq (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_035d_c7
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_eq (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_03b6_c7
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_eq (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_040f_c7
  refine rx_dest ?_
  refine rx_push (w := 0x0de0b6b3a7640000) (by decide) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_callvalue (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_lt hltz (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0470_c7
  refine rx_dest ?_
  refine rx_push (w := 1000000000) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_callvalue (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_mod hmodv (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_04cd_c7
  refine rx_dest ?_
  refine rx_push (w := 1000000000) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_callvalue (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_div (v := gweiAmount sevm) rfl (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 0xffffffffffffffff) (by decide) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt hgtz (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0535_c7
  refine rx_dest ?_
  refine rx_push (w := 96) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 1344) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_callRet (j := 25) rfl hcall1 ?_
  rw [show G + (874 + sloadCost sevm b solCountSlot) =
    (((G + 827) + 11) + sloadCost sevm b solCountSlot) + 36 by omega]
  unfold t_0540_c7
  refine rx_dest ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_push (w := BeaconDeposit.depositEventTopic)
    (by rw [BeaconDeposit.depositEventTopic_eq]; decide) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 10) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 10) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 1397) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := solCountSlot) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_sload_sel hfork (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_callRet (j := 25) rfl hcall2 k

end Blanc.Lift.BeaconDeposit
