import Blanc.Lift.BeaconDeposit.BodySignatureRoot
import Blanc.Lift.BeaconDeposit.SafeShaKit

/-!
# Safety segment B4: `signature_root`, inverted (converse of `body_signatureRoot`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- **The slice helper (entry 13), inverted**: with both bound checks passing, every run
returns `en - st :: st + x` over the caller's stack. -/
private theorem ri_slice13 {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {x len st en ret dv av : B256} {S : List B256} {o : Outcome}
    (h1 : B256.gtCheck st en = 0) (h2 : B256.gtCheck en len = 0)
    (hd : en - st = dv) (ha : st + x = av)
    (run : SFunc.Run prog sevm (St b (x :: len :: st :: en :: ret :: S) M G) t_16fe_c13 o) :
    ∃ G', o = .returned (St b (dv :: av :: S) M G') := by
  subst hd ha
  have run := run.cut
  unfold t_16fe_c13 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  rw [h1, show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  unfold t_170d_c13 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  rw [h2, show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  unfold t_1719_c13 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨G', hr⟩ := ric_ret run
  exact ⟨G', Seg.done.inj hr⟩

/-- The slice helper's call site, inverted: the continuation runs from the helper's return. -/
private theorem ric_slice13 {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    {dd x len st en ret dv av : B256} {S : List B256}
    (h1 : B256.gtCheck st en = 0) (h2 : B256.gtCheck en len = 0)
    (hd : en - st = dv) (ha : st + x = av)
    (run : SFunc.RunCut prog sevm [] (St b (dd :: x :: len :: st :: en :: ret :: S) M G)
      (.callNext 13 f) r) :
    ∃ G', SFunc.RunCut prog sevm [] (St b (dv :: av :: S) M G') f r := by
  obtain ⟨_, ⟨D, hD, run⟩ | ⟨D, hD, -⟩⟩ := ric_call prog_13 run
  · obtain ⟨G', e⟩ := ri_slice13 h1 h2 hd ha hD
    cases e
    exact ⟨G', run⟩
  · obtain ⟨G', e⟩ := ri_slice13 h1 h2 hd ha hD
    cases e

/-- **Site 1, inverted** (converse of `sig_site1`). -/
private theorem inv_site1 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP pkR : B256} {R : List B256} {r : Seg}
    (hsha : ShaReady sevm b)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 352).toBytes)
    (hpk : img.sliceD 352 32 0 = pkR.toBytes)
    (run : SFunc.RunCut prog sevm []
      (St b (0x20 :: 0x160 :: 0 :: 0x80 :: a :: rt :: 96 :: sP :: R) M G) t_086e_c12 r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (sevm.data.sliceD sP.toNat 64 0)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (sig1Img img sevm sP.toNat) ∧ M'.size = 832 ∧
      SFunc.RunCut prog sevm []
        (St b' (Nat.toB256 32 :: Nat.toB256 448 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 ::
          sP :: R) M' G') t_096a_c14 r := by
  set img1 := Bytes.writeAt img 384 (sevm.data.sliceD sP.toNat 64 0) with himg1
  set img2 := Bytes.writeAt img1 352 (Nat.toB256 64).toBytes with himg2
  set img3 := Bytes.writeAt img2 64 (Nat.toB256 448).toBytes with himg3
  set M1 := M.write 384 (sevm.data.sliceD sP.toNat 64 0) with hM1
  set M2 := M1.write 352 (Nat.toB256 64).toBytes with hM2
  set M3 := M2.write 64 (Nat.toB256 448).toBytes with hM3
  have hs1 : M1.size = 832 := by
    rw [hM1, Mem.size_write_of_le (by rw [List.length_sliceD, hs]; decide), hs]
  have hs2 : M2.size = 832 := by
    rw [hM2, Mem.size_write_word_aligned (by rw [hs1]) (by decide), hs1]; rfl
  have hs3 : M3.size = 832 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2]) (by decide), hs2]; rfl
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hr1 : Mem.Reads M1 img1 := hr.write hwf _ _
  have hr2 : Mem.Reads M2 img2 := hr1.write hwf1 _ _
  have hr3 : Mem.Reads M3 img3 := hr2.write hwf2 _ _
  have hfp1 : img1.sliceD 64 32 0 = (Nat.toB256 352).toBytes := by
    rw [himg1, sliceD_writeAt_out (by omega), hfp]
  have hfp3 : img3.sliceD 64 32 0 = (Nat.toB256 448).toBytes := by
    have := Bytes.sliceD_writeAt img2 (Nat.toB256 448).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlen3 : img3.sliceD 352 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg3, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
    have := Bytes.sliceD_writeAt img1 (Nat.toB256 64).toBytes 352
    rwa [B256.length_toBytes] at this
  have hw1 : img3.sliceD 384 32 0 = (cdWord sevm sP.toNat).toBytes := by
    rw [himg3, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1]
    simpa using sliceD_cd_word img sevm 384 sP.toNat 64 0 (by omega)
  have hw2 : img3.sliceD (384 + 32) 32 0 = (cdWord sevm (sP.toNat + 32)).toBytes := by
    rw [himg3, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1]
    exact sliceD_cd_word img sevm 384 sP.toNat 64 32 (by omega)
  have h352 : (0x160 : B256).toNat = 352 := rfl
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have t352 : (Nat.toB256 352).toNat = 352 := toNat_toB256' (by decide)
  have t384 : (Nat.toB256 384).toNat = 384 := toNat_toB256' (by decide)
  have t64 : (Nat.toB256 64).toNat = 64 := toNat_toB256' (by decide)
  unfold t_086e_c12 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h352, read_word hr 352 hpk, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨_, run⟩ := ric_slice13 (dv := Nat.toB256 64) (av := sP) (by decide) (by decide)
    (by decide) (push0_add sP) run
  unfold t_0884_c12 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 384) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_calldatacopy s1
  rw [t384, t64, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 448) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr1 64 hfp1, read_covered hs1 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 96) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t352, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr3 64 hfp3, read_covered hs3 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [t352, read_word hr3 352 hlen3, read_covered hs3 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 384) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_08bb_c12_eq] at run
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 384) (d := 448) (n := 832)
    (x1 := Nat.toB256 384) (x3 := Nat.toB256 448) (x4 := Nat.toB256 352)
    (R := 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: R)
    prog_14 (by simp) (by decide) hwf3 hr3 hs3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfp3 hw1 hw2 hsha.nodeleg hsha.warm hsha.pre hsha.fork hsha.depth run
  rw [cdWord_pair] at hpost
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; rfl, run⟩

/-- **Site 2, inverted** (converse of `sig_site2`). -/
private theorem inv_site2 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP pkR h1 : B256} {R : List B256} {r : Seg}
    (hsha : ShaReady sevm b) (hsP : sP.toNat + 96 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 448).toBytes)
    (hh1 : img.sliceD 448 32 0 = h1.toBytes)
    (run : SFunc.RunCut prog sevm []
      (St b (Nat.toB256 32 :: Nat.toB256 448 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 ::
        sP :: R) M G) t_096a_c14 r) :
    ∃ b' M' G', ShaCallPost b b'
        (Bytes.sha256 (sevm.data.sliceD (sP.toNat + 64) 32 0 ++ (0 : B256).toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (sig2Img img sevm (sP.toNat + 64)) ∧ M'.size = 832 ∧
      SFunc.RunCut prog sevm []
        (St b' (Nat.toB256 32 :: Nat.toB256 544 :: h1 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt ::
          96 :: sP :: R) M' G') t_0a66_c15 r := by
  set p := sP.toNat + 64 with hp
  set img1 := Bytes.writeAt img 480 (sevm.data.sliceD p 32 0) with himg1
  set img2 := Bytes.writeAt img1 512 (0 : B256).toBytes with himg2
  set img3 := Bytes.writeAt img2 448 (Nat.toB256 64).toBytes with himg3
  set img4 := Bytes.writeAt img3 64 (Nat.toB256 544).toBytes with himg4
  set M1 := M.write 480 (sevm.data.sliceD p 32 0) with hM1
  set M2 := M1.write 512 (0 : B256).toBytes with hM2
  set M3 := M2.write 448 (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 544).toBytes with hM4
  have hs1 : M1.size = 832 := by
    rw [hM1, Mem.size_write_of_le (by rw [List.length_sliceD, hs]; decide), hs]
  have hs2 : M2.size = 832 := by
    rw [hM2, Mem.size_write_word_aligned (by rw [hs1]) (by decide), hs1]; rfl
  have hs3 : M3.size = 832 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2]) (by decide), hs2]; rfl
  have hs4 : M4.size = 832 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs3]) (by decide), hs3]; rfl
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 : Mem.Reads M1 img1 := hr.write hwf _ _
  have hr2 : Mem.Reads M2 img2 := hr1.write hwf1 _ _
  have hr3 : Mem.Reads M3 img3 := hr2.write hwf2 _ _
  have hr4 : Mem.Reads M4 img4 := hr3.write hwf3 _ _
  have hfp2 : img2.sliceD 64 32 0 = (Nat.toB256 448).toBytes := by
    rw [himg2, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1,
      sliceD_writeAt_out (by omega), hfp]
  have hfp4 : img4.sliceD 64 32 0 = (Nat.toB256 544).toBytes := by
    have := Bytes.sliceD_writeAt img3 (Nat.toB256 544).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlen4 : img4.sliceD 448 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
    have := Bytes.sliceD_writeAt img2 (Nat.toB256 64).toBytes 448
    rwa [B256.length_toBytes] at this
  have hw1 : img4.sliceD 480 32 0 = (cdWord sevm p).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1]
    simpa using sliceD_cd_word img sevm 480 p 32 0 (by omega)
  have hw2 : img4.sliceD (480 + 32) 32 0 = (0 : B256).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2]
    have := Bytes.sliceD_writeAt img1 (0 : B256).toBytes 512
    rwa [B256.length_toBytes] at this
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have t448 : (Nat.toB256 448).toNat = 448 := toNat_toB256' (by decide)
  have t480 : (Nat.toB256 480).toNat = 480 := toNat_toB256' (by decide)
  have t512 : (Nat.toB256 512).toNat = 512 := toNat_toB256' (by decide)
  have t32 : (Nat.toB256 32).toNat = 32 := toNat_toB256' (by decide)
  have tp : (Nat.toB256 p).toNat = p := toNat_toB256' (by omega)
  unfold t_096a_c14 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [t448, read_word hr 448 hh1, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨_, run⟩ := ric_slice13 (dv := Nat.toB256 32) (av := Nat.toB256 p) (by decide)
    (by decide) (by decide) (push40_add (by omega)) run
  unfold t_097b_c14 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 480) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_calldatacopy s1
  rw [t480, tp, t32, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 512) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t512, show (Bytes.toB256 [0x00]).toBytes = (0 : B256).toBytes by decide, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr2 64 hfp2, read_covered hs2 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t448, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 544) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [t448, read_word hr4 448 hlen4, read_covered hs4 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 480) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_09b7_c14_eq] at run
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 480) (d := 544) (n := 832)
    (x1 := Nat.toB256 480) (x3 := Nat.toB256 544) (x4 := Nat.toB256 448)
    (R := h1 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: R)
    prog_15 (by simp) (by decide) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfp4 hw1 hw2 hsha.nodeleg hsha.warm hsha.pre hsha.fork hsha.depth run
  rw [cdWord_toBytes] at hpost
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; rfl, run⟩

/-- **Site 3, inverted** (converse of `sig_site3`). -/
private theorem inv_site3 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {h1 h2 : B256} {R : List B256} {r : Seg}
    (hsha : ShaReady sevm b)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 544).toBytes)
    (hh2 : img.sliceD 544 32 0 = h2.toBytes)
    (run : SFunc.RunCut prog sevm []
      (St b (Nat.toB256 32 :: Nat.toB256 544 :: h1 :: 2 :: R) M G) t_0a66_c15 r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (h1.toBytes ++ h2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (sig3Img img h1 h2) ∧ M'.size = 832 ∧
      SFunc.RunCut prog sevm [] (St b' (Nat.toB256 32 :: Nat.toB256 640 :: R) M' G')
        t_0b4c_c16 r := by
  set img1 := Bytes.writeAt img 576 h1.toBytes with himg1
  set img2 := Bytes.writeAt img1 608 h2.toBytes with himg2
  set img3 := Bytes.writeAt img2 544 (Nat.toB256 64).toBytes with himg3
  set img4 := Bytes.writeAt img3 64 (Nat.toB256 640).toBytes with himg4
  set M1 := M.write 576 h1.toBytes with hM1
  set M2 := M1.write 608 h2.toBytes with hM2
  set M3 := M2.write 544 (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 640).toBytes with hM4
  have hs1 : M1.size = 832 := by
    rw [hM1, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; rfl
  have hs2 : M2.size = 832 := by
    rw [hM2, Mem.size_write_word_aligned (by rw [hs1]) (by decide), hs1]; rfl
  have hs3 : M3.size = 832 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2]) (by decide), hs2]; rfl
  have hs4 : M4.size = 832 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs3]) (by decide), hs3]; rfl
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 : Mem.Reads M1 img1 := hr.write hwf _ _
  have hr2 : Mem.Reads M2 img2 := hr1.write hwf1 _ _
  have hr3 : Mem.Reads M3 img3 := hr2.write hwf2 _ _
  have hr4 : Mem.Reads M4 img4 := hr3.write hwf3 _ _
  have hfp2 : img2.sliceD 64 32 0 = (Nat.toB256 544).toBytes := by
    rw [himg2, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), hfp]
  have hfp4 : img4.sliceD 64 32 0 = (Nat.toB256 640).toBytes := by
    have := Bytes.sliceD_writeAt img3 (Nat.toB256 640).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlen4 : img4.sliceD 544 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
    have := Bytes.sliceD_writeAt img2 (Nat.toB256 64).toBytes 544
    rwa [B256.length_toBytes] at this
  have hw1 : img4.sliceD 576 32 0 = h1.toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1]
    have := Bytes.sliceD_writeAt img h1.toBytes 576
    rwa [B256.length_toBytes] at this
  have hw2 : img4.sliceD (576 + 32) 32 0 = h2.toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2]
    have := Bytes.sliceD_writeAt img1 h2.toBytes 608
    rwa [B256.length_toBytes] at this
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have t544 : (Nat.toB256 544).toNat = 544 := toNat_toB256' (by decide)
  have t576 : (Nat.toB256 576).toNat = 576 := toNat_toB256' (by decide)
  have t608 : (Nat.toB256 608).toNat = 608 := toNat_toB256' (by decide)
  unfold t_0a66_c15 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [t544, read_word hr 544 hh2, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 576) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t576, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 608) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t608, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr2 64 hfp2, read_covered hs2 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 0) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t544, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 640) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [t544, read_word hr4 544 hlen4, read_covered hs4 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 576) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_0a9d_c15_eq] at run
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 576) (d := 640) (n := 832)
    (x1 := Nat.toB256 576) (x3 := Nat.toB256 640) (x4 := Nat.toB256 544) (R := R)
    prog_16 (by simp) (by decide) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfp4 hw1 hw2 hsha.nodeleg hsha.warm hsha.pre hsha.fork hsha.depth run
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; rfl, run⟩

-- SEGMENT: safeSignatureRoot
/-- **Inversion of segment 4 (`t_086e_c12 → t_0b4c_c16`).**

Proof sketch.  Three instances of the inverted precompile block (segment B3's sketch), and the
slice helper (entry 13) inverted twice: its two bound checks `GT … REVERT` pass on the constants
`0 ≤ 64 ≤ 96`, `64 ≤ 96 ≤ 96`, and it returns `sP + start, end - start`.  `hsP` keeps `sP + 64`
from wrapping, so the second slice reads `sliceD (sP + 64) 32`. -/
theorem safe_signatureRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR : B256} {G : Nat}
    {M : Mem} {o : Outcome}
    (hsha : ShaReady sevm b) (hsP : sP.toNat + 96 < 2 ^ 256)
    (hM : BodyMem M 832 0x160
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x160, pkR.toBytes)])
    (run : SFunc.Run prog sevm
      (St b [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M G)
      t_086e_c12 o) :
    ∃ b' M' G', Keep b b' ∧
      BodyMem M' 832 0x280
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x280, (BeaconDeposit.signatureRoot Bytes.sha256
            (sevm.data.sliceD sP.toNat 96 0)).toBytes)] ∧
      SFunc.Run prog sevm
        (St b' [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G')
        t_0b4c_c16 o := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  have hfp0 : img.sliceD 64 32 0 = (Nat.toB256 352).toBytes := by
    rw [hfp]; rfl
  have hpk : img.sliceD 352 32 0 = pkR.toBytes := by
    have := hf (0x160, pkR.toBytes) (by simp)
    rwa [B256.length_toBytes] at this
  have h80 : img.sliceD 128 32 0 = (8 : B256).toBytes := by
    have := hf (0x80, (8 : B256).toBytes) (by simp)
    rwa [B256.length_toBytes] at this
  have ha0 : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat :=
    hf (0xa0, BeaconDeposit.le64 a.toNat) (by simp)
  set R := [(32 : B256), wP, 48, pP, 0x01b8, sel] with hR
  -- site 1
  obtain ⟨b1, M1, G1, hp1, hwf1, hr1, hs1, run⟩ :=
    inv_site1 (a := a) (rt := rt) (R := R) hsha hwf hr hs hfp0 hpk run.cut
  set I1 := sig1Img img sevm sP.toNat
  set h1 := Bytes.sha256 (sevm.data.sliceD sP.toNat 64 0)
  have hK1 := Keep.of_sha hp1
  have hI1fp : I1.sliceD 64 32 0 = (Nat.toB256 448).toBytes := by
    simp only [I1, sig1Img]
    rw [shaImg_out (by omega)]
    have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt img 384
      (sevm.data.sliceD sP.toNat 64 0)) 352 (Nat.toB256 64).toBytes) (Nat.toB256 448).toBytes 64
    rwa [B256.length_toBytes] at this
  have hI1h : I1.sliceD 448 32 0 = h1.toBytes := by
    simp only [I1, sig1Img]
    rw [shaImg_digest, cdWord_pair]
  -- site 2
  obtain ⟨b2, M2, G2, hp2, hwf2, hr2, hs2, run⟩ :=
    inv_site2 (hsha.keep hK1) hsP hwf1 hr1 hs1 hI1fp hI1h run
  set I2 := sig2Img I1 sevm (sP.toNat + 64)
  set h2 := Bytes.sha256 (sevm.data.sliceD (sP.toNat + 64) 32 0 ++ (0 : B256).toBytes)
  have hK2 := Keep.of_sha hp2
  have hI2fp : I2.sliceD 64 32 0 = (Nat.toB256 544).toBytes := by
    simp only [I2, sig2Img]
    rw [shaImg_out (by omega)]
    have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt I1 480
      (sevm.data.sliceD (sP.toNat + 64) 32 0)) 512 (0 : B256).toBytes) 448
      (Nat.toB256 64).toBytes) (Nat.toB256 544).toBytes 64
    rwa [B256.length_toBytes] at this
  have hI2h : I2.sliceD 544 32 0 = h2.toBytes := by
    simp only [I2, sig2Img]
    rw [shaImg_digest, cdWord_toBytes]
  -- site 3
  obtain ⟨b3, M3, G3, hp3, hwf3, hr3, hs3, run⟩ :=
    inv_site3 ((hsha.keep hK1).keep hK2) hwf2 hr2 hs2 hI2fp hI2h run
  have hK3 := Keep.of_sha hp3
  set I3 := sig3Img I2 h1 h2
  have hout : ∀ st len, 96 ≤ st → st + len ≤ 352 → I3.sliceD st len 0 = img.sliceD st len 0 := by
    intro st len h1' h2'
    simp only [I3, sig3Img, I2, sig2Img, I1, sig1Img]
    rw [shaImg_out (by omega), sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      shaImg_out (by omega), sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [List.length_sliceD]; omega),
      shaImg_out (by omega), sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [List.length_sliceD]; omega)]
  refine ⟨b3, M3, G3, hK1.trans (hK2.trans hK3), ⟨hwf3, hs3, I3, hr3, ?_, ?_⟩, run.uncut⟩
  · simp only [I3, sig3Img]
    rw [shaImg_out (by omega)]
    have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt I2 576
      h1.toBytes) 608 h2.toBytes) 544 (Nat.toB256 64).toBytes) (Nat.toB256 640).toBytes 64
    rw [B256.length_toBytes] at this
    rw [this]; rfl
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [B256.length_toBytes]; exact (hout 128 32 (by omega) (by omega)).trans h80
    · exact (hout 160 8 (by omega) (by omega)).trans ha0
    · rw [B256.length_toBytes]
      simp only [I3, sig3Img]
      rw [shaImg_digest, signatureRoot_eq]

end Blanc.Lift.BeaconDeposit
