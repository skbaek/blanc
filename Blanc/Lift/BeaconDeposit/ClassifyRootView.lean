import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.Lift.BeaconDeposit.RootView
import Blanc.Lift.BeaconDeposit.BodyShaKit
import Blanc.Lift.BeaconDeposit.HistSafeWorld
import Blanc.Lift.BeaconDeposit.SafeLittleEndian
import Blanc.Lift.InvWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WalkInvKit

/-!
# Historical classification of `get_deposit_root()` on the deployed runtime

Inverts any successful historical frame execution of the deployed runtime whose selector is
`getDepositRootSelector`: without warm-slot, depth, gas-sufficiency, or `CoveredFork` premises,
`sevm.value = 0`, `post.output` is `(Acc.root sha256 (solAcc (pre.getStor sevm.currentTarget))).toBytes`,
and every account's storage map and log list are preserved.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc.BeaconDeposit

private theorem loopBaseH_baseRel {b₀ b : Devm} (h : LoopBaseH b₀ b) : BaseRel b₀ b :=
  ⟨h.stor, h.code, h.addrs, h.logs, h.output, h.error⟩

private theorem safe_root_join {sevm : Sevm} {b : Devm} {h s : Nat} {x : B256}
    {R : List B256} {M : Mem} {G : Nat} {r : Seg}
    (hh : h < 32) (hs : s < 2 ^ 32)
    (run : SFunc.RunCut prog sevm [24] (St b (Nat.toB256 h :: Nat.toB256 s :: x :: R) M G)
      t_12e2_c5 r) :
    ∃ Gf, r = .at 24 (St b (Nat.toB256 (h + 1) :: Nat.toB256 (s / 2) :: x :: R) M Gf) := by
  unfold t_12e2_c5 at run
  winv 3
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (s / 2))
    (by rw [show Bytes.toB256 [0x02] = (2 : B256) by decide, toB256_div_two (by omega)])
    (ri_div s1)
  winv 3
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (h + 1)) (one_add_toB256 (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  exact ric_jumpCut (by simp only [List.mem_cons, List.not_mem_nil, or_false]) run

private theorem safe_root_iterH {sevm : Sevm} {b₀ b : Devm} {h size : Nat} {node : B256}
    {R : List B256} {M : Mem} {img : Bytes} {G : Nat} {r : Seg}
    (hL : LoopBaseH b₀ b) (hsha : ShaReadyRules sevm b)
    (hh : h < 32) (hsize : size < 2 ^ 32)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = rootMemSize h)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 (rootFp h)).toBytes)
    (run : SFunc.RunCut prog sevm [24] (St b (Nat.toB256 h :: Nat.toB256 size :: node :: R) M G)
      t_10d1_c24 r) :
    ∃ b' M' G' img', LoopBaseH b₀ b' ∧ Mem.Wf M' ∧ M'.size = rootMemSize (h + 1) ∧
      Mem.Reads M' img' ∧ img'.sliceD 64 32 0 = (Nat.toB256 (rootFp (h + 1))).toBytes ∧
      r = .at 24 (St b' (Nat.toB256 (h + 1) :: Nat.toB256 (size / 2) ::
        rootNode sevm b size h node :: R) M' G') := by
  have h20 : Bytes.toB256 [0x20] = Nat.toB256 32 := by decide
  have hlt : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 1 := by
    rw [h20, lt_toB256 (by omega) (by norm_num only)]; simp only [hh, ↓reduceIte]
  have hand : (Bytes.toB256 [0x01] &&& Nat.toB256 size) = Nat.toB256 (size % 2) := by
    rw [show Bytes.toB256 [0x01] = 1 by decide]
    exact Blanc.one_and_toB256_eq_mod_two size (by omega)
  unfold t_10d1_c24 at run
  winv 5
  rw [hlt, show B256.eqCheck (1 : B256) 0 = 0 by decide] at run
  winv 1
  rcases ric_branch run with ⟨-, _, run⟩ | ⟨hw, -⟩
  swap; · exact absurd hw (by decide)
  unfold t_10db_c24 at run
  winv 2
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (size % 2)) hand (ri_and s1)
  winv 2
  rw [eq_one_mod_two] at run
  winv 2
  have hn_mod := rootMemSize_mod h
  have hn_ge := rootMemSize_ge h
  have hn_le := rootMemSize_le h
  have hF : (Nat.toB256 (rootFp h + 96)).toNat = rootFp h + 96 :=
    toNat_toB256' (by unfold rootFp; omega)
  rcases Nat.mod_two_eq_zero_or_one size with heven | hodd
  · -- dead bit (`size % 2 = 0`)
    simp only [heven, zero_ne_one, ↓reduceIte,
      show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
    rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
    · exact absurd hw (by decide)
    unfold t_11e6_c24 at run
    winv 8
    rw [hlt] at run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
    rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
    · exact absurd hw (by decide)
    rw [t_11f6_eq] at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    have hkey : Nat.toB256 h + Bytes.toB256 [0x21] = solZeroHashSlot h := by
      apply B256.toNat_inj
      rw [B256.toNat_add, toNat_toB256' (by omega),
        show (Bytes.toB256 [0x21]).toNat = 33 by decide,
        Nat.add_comm, Nat.lo_eq_of_lt (by omega), solZeroHashSlot, toNat_toB256' (by omega)]
    obtain ⟨_, rfl⟩ := ri_val (w := solZeroHashSlot h) hkey (ri_add s1)
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sloadH hsha.bal s1
    set b1 := afterSloadH sevm b (solZeroHashSlot h) with hb1
    have hok1 : ShaReadyRules sevm b1 := ⟨by rw [hb1, afterSloadH_getCode]; exact hsha.nodeleg,
      by rw [hb1, afterSloadH_accessedAddresses]; exact hsha.warm, hsha.pre, hsha.sg, hsha.bal⟩
    set zh := b.getStorVal sevm.currentTarget (solZeroHashSlot h) with hzh
    obtain ⟨b', M', _, hpost, hwf', hr', hs', run⟩ :=
      ric_pack_shaH_of_delegation (a := node) (bw := zh)
        (n := rootMemSize h) (f := rootFp h) prog_28
        (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
          not_false_eq_true])
        (by decide) hwf hr hs hn_mod hn_ge hn_le (by unfold rootFp; omega)
        (by unfold rootFp; omega) (by unfold rootFp; omega) hfp
        hok1.nodeleg hok1.warm hok1.pre hok1.sg run
    unfold t_12dd_c24 at run
    winv 3
    rw [hF, read_word hr' _ shaImg_digest,
      read_covered hs' (by unfold rootFp; omega) (by omega)] at run
    winv 2
    obtain ⟨Gf, hr_out⟩ := safe_root_join hh hsize run
    have hnode : hashPair Bytes.sha256 node zh = rootNode sevm b size h node := by
      simp only [rootNode, heven, zero_ne_one, ↓reduceIte, hzh, hashPair]
    rw [show Bytes.sha256 (node.toBytes ++ zh.toBytes) = rootNode sevm b size h node from hnode]
      at hr_out
    refine ⟨b', M', Gf, _, hL.step (Keep.of_sha hpost), hwf', by rw [hs', rootMemSize_succ],
      hr', ?_, hr_out⟩
    rw [shaImg_out (by unfold rootFp; omega), packImg_word64 (by unfold rootFp; omega), rootFp_succ]
  · -- live bit (`size % 2 = 1`)
    simp only [hodd, ↓reduceIte,
      show B256.eqCheck (1 : B256) 0 = 0 by decide] at run
    rcases ric_branch run with ⟨-, _, run⟩ | ⟨hw, -⟩
    swap; · exact absurd hw (by decide)
    unfold t_10e7_c24 at run
    winv 6
    rw [hlt] at run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
    rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
    · exact absurd hw (by decide)
    rw [t_10f5_eq] at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    have hkey : Nat.toB256 h + Bytes.toB256 [0x00] = solBranchSlot h := by
      apply B256.toNat_inj
      rw [B256.toNat_add, toNat_toB256' (by omega),
        show (Bytes.toB256 [0x00]).toNat = 0 by decide,
        Nat.add_zero, Nat.lo_eq_of_lt (by omega), solBranchSlot, toNat_toB256' (by omega)]
    obtain ⟨_, rfl⟩ := ri_val (w := solBranchSlot h) hkey (ri_add s1)
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sloadH hsha.bal s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
    set b1 := afterSloadH sevm b (solBranchSlot h) with hb1
    have hok1 : ShaReadyRules sevm b1 := ⟨by rw [hb1, afterSloadH_getCode]; exact hsha.nodeleg,
      by rw [hb1, afterSloadH_accessedAddresses]; exact hsha.warm, hsha.pre, hsha.sg, hsha.bal⟩
    set br := b.getStorVal sevm.currentTarget (solBranchSlot h) with hbr
    obtain ⟨b', M', _, hpost, hwf', hr', hs', run⟩ :=
      ric_pack_shaH_of_delegation (a := br) (bw := node)
        (n := rootMemSize h) (f := rootFp h) prog_27
        (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
          not_false_eq_true])
        (by decide) hwf hr hs hn_mod hn_ge hn_le (by unfold rootFp; omega)
        (by unfold rootFp; omega) (by unfold rootFp; omega) hfp
        hok1.nodeleg hok1.warm hok1.pre hok1.sg run
    unfold t_11dd_c24 at run
    winv 3
    rw [hF, read_word hr' _ shaImg_digest,
      read_covered hs' (by unfold rootFp; omega) (by omega)] at run
    winv 3
    obtain ⟨_, run⟩ := ric_jump
      (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
        not_false_eq_true]) prog_5 run
    obtain ⟨Gf, hr_out⟩ := safe_root_join hh hsize run
    have hnode : hashPair Bytes.sha256 br node = rootNode sevm b size h node := by
      simp only [rootNode, hodd, ↓reduceIte, hbr, hashPair]
    rw [show Bytes.sha256 (br.toBytes ++ node.toBytes) = rootNode sevm b size h node from hnode]
      at hr_out
    refine ⟨b', M', Gf, _, hL.step (Keep.of_sha hpost), hwf', by rw [hs', rootMemSize_succ],
      hr', ?_, hr_out⟩
    rw [shaImg_out (by unfold rootFp; omega), packImg_word64 (by unfold rootFp; omega), rootFp_succ]

private theorem safe_root_exitH {sevm : Sevm} {b₀ b : Devm} {node rv ret : B256} {count : Nat}
    {R0 : List B256} {M : Mem} {img : Bytes} {G : Nat} {r : Seg}
    (hL : LoopBaseH b₀ b) (hsha : ShaReadyRules sevm b)
    (hcount : b.getStorVal sevm.currentTarget solCountSlot = Nat.toB256 count)
    (hc32 : count < 2 ^ 32)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 3296)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 3200).toBytes)
    (run : SFunc.RunCut prog sevm [24]
      (St b (Nat.toB256 32 :: Nat.toB256 0 :: node :: rv :: ret :: R0) M G) t_10d1_c24 r) :
    ∃ bF MF Gf imgF, LoopBaseH b₀ bF ∧ Mem.Wf MF ∧ MF.size = 3456 ∧
      Mem.Reads MF imgF ∧ imgF.sliceD 64 32 0 = (Nat.toB256 3360).toBytes ∧
      r = .done (.returned (St bF (mixIn Bytes.sha256 node count :: R0) MF Gf)) := by
  set R := rv :: ret :: R0
  have hpB : (Nat.toB256 3200).toNat = 3200 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hcnt : b.getStorVal sevm.currentTarget (Bytes.toB256 [0x20]) = Nat.toB256 count := by
    rw [show Bytes.toB256 [0x20] = solCountSlot by decide, hcount]
  unfold t_10d1_c24 at run
  winv 6
  rw [show B256.ltCheck (Nat.toB256 32) (Bytes.toB256 [0x20]) = 0 by decide,
    show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  unfold t_12f0_c24 at run
  winv 6
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sloadH hsha.bal s1
  rw [hcnt] at run
  set b1 := afterSloadH sevm b (Bytes.toB256 [0x20]) with hb1
  have hL1 : LoopBaseH b₀ b1 := hL.step (Keep.refl _)
  have hok1 : ShaReadyRules sevm b1 := ⟨by rw [hb1, afterSloadH_getCode]; exact hsha.nodeleg,
    by rw [hb1, afterSloadH_accessedAddresses]; exact hsha.warm, hsha.pre, hsha.sg, hsha.bal⟩
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨_, ⟨D, hle, run⟩ | ⟨D, hle, -⟩⟩ :=
    ric_call (k := 25) (hk := (show prog[25]? = some t_14ba_c25 from rfl)) run
  swap
  · exact (safe_to_little_endian_64_not_halted_any_data hwf hr
      (by simp only [hs, Nat.reduceMod]) (by simp only [hs, Nat.reduceLeDiff])
      (by rw [hfp, B256.toB256_toBytes]) (by simp only [hpB, Nat.reduceMod])
      (by simp only [hpB, Nat.reduceLeDiff])
      (by simp only [hpB, Nat.reduceAdd, Nat.reducePow, Nat.reduceLT]) hle).elim
  obtain ⟨M1, G1, rfl, hwf1, hr1, hs1⟩ :=
    safe_to_little_endian_64_returned_any_data hwf hr
      (by simp only [hs, Nat.reduceMod]) (by simp only [hs, Nat.reduceLeDiff])
      (by rw [hfp, B256.toB256_toBytes]) (by simp only [hpB, Nat.reduceMod])
      (by simp only [hpB, Nat.reduceLeDiff])
      (by simp only [hpB, Nat.reduceAdd, Nat.reducePow, Nat.reduceLT]) hle
  rw [hs, hpB, show max 3296 (3200 + 64) = 3296 by decide] at hs1
  set img1 := leImg img (Nat.toB256 3200) (Nat.toB256 count) with himg1
  have h1_64 : img1.sliceD 64 32 0 = (Nat.toB256 3264).toBytes := by
    rw [himg1, leImg, hpB, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self]
    rfl
  have h1_len : img1.sliceD 3200 32 0 = (Nat.toB256 8).toBytes := by
    rw [himg1, leImg, hpB, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), sliceD_word_self]
    rfl
  set M2 := M1.write 3296 node.toBytes with hM2
  have hs2 : M2.size = 3328 := by
    rw [hM2, Mem.size_write_word_aligned (by rw [hs1]) (by decide), hs1]; decide
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hr2 := hr1.write hwf1 3296 node.toBytes
  have h2_len : (Bytes.writeAt img1 3296 node.toBytes).sliceD 3200 32 0 =
      (Nat.toB256 8).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), h1_len]
  set ws := Bytes.toB256 (M2.read 3232 32).1 with hws
  set M2' := (M2.read 3328 32).2 with hM2'
  have hs2' : M2'.size = 3360 := by rw [hM2', read_ext_size hs2 (by decide) (by decide)]; decide
  have hwd : Bytes.toB256 (M2.read 3328 32).1 = 0 := by
    rw [read_past_size hwf2 (by rw [hs2])]; decide
  set m := Bytes.toB256 (255 :: List.replicate 31 255) +
    B256.bexp (Bytes.toB256 [0x01, 0x00]) (Nat.toB256 24) with hm
  have hmask : (~~~ m) = maskTop8 := by rw [hm]; decide +kernel
  set M3 := M2'.write 3328 (ws &&& ~~~ m).toBytes with hM3
  set M4 := M3.write 3336 (0 : B256).toBytes with hM4
  have hs3 : M3.size = 3360 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2']) (by decide), hs2']; decide
  have hs4 : M4.size = 3392 := by rw [hM4, Mem.size_write_word_at, hs3]; decide
  have hwf3 : Mem.Wf M3 := (hwf2.extend _ _).write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr3 := (hr2.extend 3328 32).write (hwf2.extend _ _) 3328 (ws &&& ~~~ m).toBytes
  have hr4 := hr3.write hwf3 3336 (0 : B256).toBytes
  set img4 := Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img1 3296 node.toBytes) 3328
    (ws &&& ~~~ m).toBytes) 3336 (0 : B256).toBytes with himg4
  have h4_64 : img4.sliceD 64 32 0 = (Nat.toB256 3264).toBytes := by
    rw [himg4, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), h1_64]
  set M5 := M4.write 3264 (Nat.toB256 64).toBytes with hM5
  set M6 := M5.write 64 (Nat.toB256 3360).toBytes with hM6
  have hs5 : M5.size = 3392 := by
    rw [hM5, Mem.size_write_word_aligned (by rw [hs4]) (by decide), hs4]; decide
  have hs6 : M6.size = 3392 := by
    rw [hM6, Mem.size_write_word_aligned (by rw [hs5]) (by decide), hs5]; decide
  have hwf5 : Mem.Wf M5 := hwf4.write _ _
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr5 := hr4.write hwf4 3264 (Nat.toB256 64).toBytes
  have hr6 := hr5.write hwf5 64 (Nat.toB256 3360).toBytes
  have h5_len : (Bytes.writeAt img4 3264 (Nat.toB256 64).toBytes).sliceD 3264 32 0 =
      (Nat.toB256 64).toBytes := sliceD_word_self _ _ _
  set img6 := Bytes.writeAt (Bytes.writeAt img4 3264 (Nat.toB256 64).toBytes) 64
    (Nat.toB256 3360).toBytes with himg6
  have h6_64 : img6.sliceD 64 32 0 = (Nat.toB256 3360).toBytes := sliceD_word_self _ _ _
  have h6_len : img6.sliceD 3264 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg6, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), h5_len]
  have hval : (ws &&& ~~~ m).toBytes = ws.toBytes.take 8 ++ List.replicate 24 0 := by
    rw [hmask, B256.and_comm, maskTop8_and]
  have h6_node : img6.sliceD 3296 32 0 = node.toBytes := by
    rw [himg6, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]), himg4,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self]
  have h6_w2 : img6.sliceD (3296 + 32) 32 0 = (ws &&& ~~~ m).toBytes := by
    rw [himg6, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), himg4,
      show (32 : Nat) = 8 + 24 from rfl, List.sliceD_split,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega), hval]
    have ht : (ws.toBytes.take 8).length = 8 := by
      simp only [List.length_take, B256.length_toBytes, Nat.reduceLeDiff, inf_of_le_left]
    rw [show B256.toBytes 0 = List.replicate 32 0 by decide]
    simp only [List.sliceD, show 3296 + (8 + 24) - 3328 = 0 from rfl, List.drop_zero]
    rw [List.takeD_eq_take 0 (by simp only [List.reduceReplicate, List.length_append, ht,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]),
      List.take_left' ht,
      List.takeD_eq_take 0 (by simp only [List.reduceReplicate, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, Nat.reduceLeDiff]),
      List.take_replicate]
    rfl
  -- Invert t_12ff_c24 up to mcpy_exit
  unfold t_12ff_c24 at run
  winv 4
  rw [show (Bytes.toB256 [0x00] : B256) <<< (Bytes.toB256 [0x40]).toNat = 0 by decide] at run
  winv 2
  rw [h40, read_word hr1 64 h1_64, read_covered hs1 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 3296) (by decide) (ri_add s1)
  winv 4
  rw [show (Nat.toB256 3296).toNat = 3296 by decide, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 3328) (by decide) (ri_add s1)
  winv 3
  rw [hpB, read_word hr2 3200 h2_len, read_covered hs2 (by decide) (by decide)] at run
  winv 2
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 3232) (by decide) (ri_add s1)
  winv 4
  obtain ⟨_, run⟩ := ric_mcpy_exit (s := 3232) (d := 3328) (l := 8) (by omega) run
  -- Invert t_135a_c24
  unfold t_135a_c24 at run
  winv 2
  rw [show (Nat.toB256 3232).toNat = 3232 by decide, ← hws,
    read_covered hs2 (by decide) (by decide)] at run
  winv 2
  rw [show (Nat.toB256 3328).toNat = 3328 by decide, hwd, ← hM2'] at run
  winv 3
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 24) (by decide) (ri_sub s1)
  winv 3
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := m) rfl (ri_add s1)
  winv 7
  rw [b256_and_zero m] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := ws &&& ~~~ m) (b256_zero_or _) (ri_or s1)
  winv 2
  rw [show (Nat.toB256 3328).toNat = 3328 by decide, ← hM3] at run
  winv 5
  rw [b256_and_zero _] at run
  winv 1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 3336) (by decide) (ri_add s1)
  winv 3
  rw [show (Nat.toB256 3336).toNat = 3336 by decide, ← hM4] at run
  winv 4
  rw [h40, read_word hr4 64 h4_64, read_covered hs4 (by decide) (by decide)] at run
  winv 2
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 72) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64) (by decide) (ri_add s1)
  winv 2
  rw [show (Nat.toB256 3264).toNat = 3264 by decide, ← hM5] at run
  winv 3
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 3360) (by decide) (ri_add s1)
  winv 4
  rw [h40, ← hM6] at run
  winv 2
  rw [show (Nat.toB256 3264).toNat = 3264 by decide, read_word hr6 3264 h6_len,
    read_covered hs6 (by decide) (by decide)] at run
  winv 8
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 3296) (by decide) (ri_add s1)
  winv 5
  rw [t_1402_eq] at run
  obtain ⟨bF, MF, _, hpost, hwfF, hrF, hsF, run⟩ :=
    ric_copy_shaH_of_delegation (n := 3392) (s := 3296) (d := 3360)
      (w1 := node) (w2 := ws &&& ~~~ m)
      (x1 := Nat.toB256 3296) (x3 := Nat.toB256 3360) (x4 := Nat.toB256 3264)
      prog_30
      (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
        not_false_eq_true])
      (by decide) hwf6 hr6 hs6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) h6_64 h6_node h6_w2 hok1.nodeleg hok1.warm hok1.pre hok1.sg run
  have hle8 : ws.toBytes.take 8 = Blanc.BeaconDeposit.le64 count := by
    have h8 : (Blanc.BeaconDeposit.le64 count).length = 8 := rfl
    rw [hws, toBytes_read, hr2.read, show (32 : Nat) = 8 + 24 from rfl, List.sliceD_split,
      List.take_left' (List.length_sliceD _ _ _ _),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      himg1, leImg, hpB, show (3200 + 32 : Nat) = 3232 from rfl,
      B256.toNat_toB256_of_lt (show count < 2 ^ 256 by omega), ← h8, Bytes.sliceD_writeAt]
  have hroot : Bytes.sha256 (node.toBytes ++ (ws &&& ~~~ m).toBytes) =
      mixIn Bytes.sha256 node count := by
    rw [hval, hle8, mixIn, zeros, List.append_assoc]
  unfold t_14b1_c24 at run
  winv 3
  rw [show (Nat.toB256 3360).toNat = 3360 by decide,
    read_word hrF 3360 shaImg_digest,
    read_covered hsF (by omega) (by omega), hroot] at run
  winv 5
  obtain ⟨Gf, hr_ret⟩ := ric_ret run
  have hLF : LoopBaseH b₀ bF := by
    have hk := Keep.of_sha hpost
    exact ⟨fun a => (hk.stor a).trans (hL1.stor a),
      fun a => (hk.code a).trans (hL1.code a),
      hk.addrs.trans hL1.addrs,
      hk.logs.trans hL1.logs,
      hk.output.trans hL1.output,
      hk.error.trans hL1.error⟩
  refine ⟨bF, MF, Gf, _, hLF, hwfF, by rw [hsF]; decide, hrF, ?_, hr_ret⟩
  rw [shaImg_out (by decide), h6_64]

private theorem safe_root_fnH {sevm : Sevm} {base : Devm} {stor : Stor} {count : Nat}
    {ret : B256} {R0 : List B256} {G : Nat} {o : Outcome}
    (hsha : ShaReadyRules sevm base)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue : stor.get solCountSlot = Nat.toB256 count) (hc32 : count < 2 ^ 32)
    (hzero : SolZeroHashesCorrect stor)
    (run : SFunc.Run prog sevm (St base (ret :: R0) mem0 G) t_10c7_c10 o) :
    ∃ bF MF Gf imgF, LoopBaseH base bF ∧ Mem.Wf MF ∧ MF.size = 3456 ∧
      Mem.Reads MF imgF ∧ imgF.sliceD 64 32 0 = (Nat.toB256 3360).toBytes ∧
      o = .returned (St bF (Acc.root Bytes.sha256 (solAcc stor) :: R0) MF Gf) := by
  have h20 : Bytes.toB256 [0x20] = solCountSlot := by decide
  have hcnt : base.getStorVal sevm.currentTarget solCountSlot = Nat.toB256 count := by
    show (Devm.getStor base sevm.currentTarget).get solCountSlot = _
    rw [hstor, hcountValue]
  have runC := run.cut
  unfold t_10c7_c10 at runC
  winv 2 at runC
  rw [h20] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_sloadH hsha.bal s1
  rw [hcnt] at runC
  winv 5 at runC
  rw [t_10d1_c10_eq] at runC
  have runL := runC.uncut
  simp only [Fin.isValue, Fin.val_zero, List.set_cons_zero] at runL
  set b1 := afterSloadH sevm base solCountSlot
  have hL0 : LoopBaseH base b1 := (LoopBaseH.refl base).step (Keep.refl _)
  let R : List B256 := Bytes.toB256 [0x00] :: ret :: R0
  let I : Devm → Prop := fun devm => ∃ h bh Mh Gh img,
    devm = St bh (Nat.toB256 h :: Nat.toB256 (count / 2 ^ h) ::
      climb Bytes.sha256 (solAcc stor).branch h 0 count 0 :: R) Mh Gh ∧
      h ≤ 32 ∧ LoopBaseH base bh ∧ Mem.Wf Mh ∧ Mh.size = rootMemSize h ∧
      Mem.Reads Mh img ∧ img.sliceD 64 32 0 = (Nat.toB256 (rootFp h)).toBytes
  let Q : Outcome → Prop := fun out => ∃ bF MF Gf imgF,
    LoopBaseH base bF ∧ Mem.Wf MF ∧ MF.size = 3456 ∧
      Mem.Reads MF imgF ∧ imgF.sliceD 64 32 0 = (Nat.toB256 3360).toBytes ∧
      out = .returned (St bF (Acc.root Bytes.sha256 (solAcc stor) :: R0) MF Gf)
  refine SFunc.RunP.loop (P := Ninst.Run) (k := 24) (g := t_10d1_c24) prog_24 I Q ?_ _ o
    ⟨0, b1, mem0, _, img0,
      by simp only [R, pow_zero, Nat.div_one, climb,
        show Bytes.toB256 [0x00] = (0 : B256) by decide,
        show Nat.toB256 0 = (0 : B256) by decide]; rfl,
      by omega, hL0, wf_mem0, mem0_size, reads_mem0, img0_word⟩ runL
  intro devm ⟨h, bh, Mh, Gh, img, hdevm, hh, hL, hwf, hs, hr, hfp⟩ r hrun
  subst hdevm
  have hshah : ShaReadyRules sevm bh := hsha.of_eq hL.code hL.addrs
  by_cases hh32 : h < 32
  · have hsz : count / 2 ^ h < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hc32
    obtain ⟨b', M', G', img', hL', hwf', hs', hr', hfp', hr_step⟩ :=
      safe_root_iterH hL hshah hh32 hsz hwf hr hs hfp hrun
    have hc := climb_succ Bytes.sha256 (solAcc stor).branch h 0 count 0
    rw [Nat.zero_add] at hc
    rw [div_pow_div_two, rootNode_eq (loopBaseH_baseRel hL) hstor hzero hh32, ← hc] at hr_step
    rcases hr_step
    exact ⟨h + 1, b', M', G', img', rfl, by omega, hL', hwf', hs', hr', hfp'⟩
  · have h_eq : h = 32 := by omega
    subst h_eq
    have hdiv : count / 2 ^ 32 = 0 := Nat.div_eq_of_lt hc32
    rw [hdiv] at hrun
    have hcb : bh.getStorVal sevm.currentTarget solCountSlot = Nat.toB256 count := by
      show (Devm.getStor bh sevm.currentTarget).get solCountSlot = _
      rw [hL.stor, hstor, hcountValue]
    obtain ⟨bF, MF, Gf, imgF, hLF, hwfF, hsF, hrF, hfpF, hr_done⟩ :=
      safe_root_exitH hL hshah hcb hc32 hwf hr hs hfp hrun
    rw [acc_root_eq hcountValue hc32] at hr_done
    rcases hr_done
    exact ⟨bF, MF, Gf, imgF, hLF, hwfF, hsF, hrF, hfpF, rfl⟩

/-- Historical classification of `get_deposit_root()` on the deployed runtime. -/
theorem root_frame_effectH {sevm : Sevm} {pre post : Devm} {history : List B256}
    (image : sevm.code = code) (fork : HistFork sevm.benvStat.fork)
    (calldata : sevm.data.length < 2 ^ 256)
    (fresh : Exec.FreshEntry sevm pre) (sha : ShaReadyRules sevm pre)
    (invariant : SolInv (pre.getStor sevm.currentTarget) history)
    (selected : Sevm.selector sevm = BeaconDeposit.getDepositRootSelector)
    (run : Exec 0 sevm pre (.ok post)) :
    sevm.value = 0 ∧
    post.output = (BeaconDeposit.Acc.root Bytes.sha256
      (solAcc (pre.getStor sevm.currentTarget))).toBytes ∧
    (∀ a, post.getStor a = pre.getStor a) ∧ post.logs = pre.logs := by
  have _ := calldata
  obtain ⟨f, hf, srun⟩ := lift_sound_noStateGas cert_check image fork.stateGas_none run
  have hf0 : prog[0]? = some t_0000_c0 := rfl
  rw [hf0] at hf
  cases hf
  rw [St.self fresh.1 fresh.2] at srun
  obtain ⟨k, G1, g, -, -, -, -, hk34, hg, srun⟩ := safe_dispatch_full srun
  have hk' : k = 34 := hk34.mpr selected
  subst hk'
  have hg34 : g = t_0244_c34 := by
    have : prog[34]? = some t_0244_c34 := rfl
    rw [this] at hg; exact (Option.some.inj hg).symm
  subst hg34
  have hw := view_worldH fork.stateGas_none (by decide) hg srun
  have hstor_all : ∀ a, post.getStor a = pre.getStor a := fun a => congrFun hw.1 a
  have hlogs : post.logs = pre.logs := hw.2
  set stor := pre.getStor sevm.currentTarget with hstor_def
  have hc32 : history.length < 2 ^ 32 := invariant.2.2.1
  have hcountVal : stor.get solCountSlot = Nat.toB256 history.length := by
    apply B256.toNat_inj
    rw [show (stor.get solCountSlot).toNat = (solAcc stor).count from rfl,
      invariant.2.1, B256.toNat_toB256_of_lt (by omega)]
  have runC := srun.cut
  unfold t_0244_c34 at runC
  winv 5 at runC
  rcases ric_branch runC with ⟨-, _, runC⟩ | ⟨hw_val, _, runC⟩
  · exact (runC.false_of_noOk (by decide)).elim
  have hval : sevm.value = 0 := eq_zero_of_iszero_ne_zero hw_val
  unfold t_0250_c34 at runC
  winv 4 at runC
  obtain ⟨_, ⟨D, hfn, runC⟩ | ⟨D, hfn, -⟩⟩ :=
    ric_call (k := 10) (hk := (show prog[10]? = some t_10c7_c10 from rfl)) runC
  swap
  · obtain ⟨_, _, _, _, -, -, -, -, -, ho⟩ :=
      safe_root_fnH sha rfl hcountVal hc32 invariant.1 hfn
    cases ho
  obtain ⟨bF, MF, Gf, imgF, _, hwfF, hsF, hrF, hfpF, ho⟩ :=
    safe_root_fnH sha rfl hcountVal hc32 invariant.1 hfn
  cases ho
  set root := Acc.root Bytes.sha256 (solAcc stor)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have h3360 : (Nat.toB256 3360).toNat = 3360 := by decide
  set MF' := MF.write 3360 root.toBytes with hMF'
  have hsF' : MF'.size = 3456 := by
    rw [hMF', Mem.size_write_word_aligned (by rw [hsF]) (by decide), hsF]; decide
  have hr' := hrF.write hwfF 3360 root.toBytes
  have hfp' : (Bytes.writeAt imgF 3360 root.toBytes).sliceD 64 32 0 =
      (Nat.toB256 3360).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfpF]
  unfold t_0259_c34 at runC
  winv 4 at runC
  rw [h40, read_word hrF 64 hfpF, read_covered hsF (by decide) (by decide)] at runC
  winv 3 at runC
  rw [h3360, ← hMF'] at runC
  winv 1 at runC
  rw [h40, read_word hr' 64 hfp', read_covered hsF' (by decide) (by decide)] at runC
  winv 3 at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add s1)
  winv 1 at runC
  cases runC with
  | last hret =>
      have hout := (ri_return hret).1
      rw [h3360, show (32 : B256).toNat = 32 by decide, hr'.read, sliceD_word_self] at hout
      exact ⟨hval, hout, hstor_all, hlogs⟩

end Blanc.Lift.BeaconDeposit
