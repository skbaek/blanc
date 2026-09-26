import Blanc.Lift.BeaconDeposit.BodyShaKit

/-!
# Body segment 4: `signature_root`

From `0x086e` (tree `t_086e_c12`, `pubkey_root` in memory) through the three hashes of
`signature_root` to the return-size check's continuation at `0x0b4c` (tree `t_0b4c_c16`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## Site 1: `sha256(signature[:64])` -/

/-- The image after site 1: the 64 signature bytes at `0x180`, the length at `0x160`, the
free pointer `0x1c0`, the digest at `0x1c0`. -/
def sig1Img (img : Bytes) (sevm : Sevm) (sP : Nat) : Bytes :=
  shaImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 384 (sevm.data.sliceD sP 64 0)) 352
    (Nat.toB256 64).toBytes) 64 (Nat.toB256 448).toBytes) 448 (cdWord sevm sP) (cdWord sevm (sP + 32))

theorem sig_site1 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP pkR : B256} {R : List B256}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : R.length ≤ 20) (hG : G + 256 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 352).toBytes)
    (hpk : img.sliceD 352 32 0 = pkR.toBytes) :
    ∃ b' M', ShaCallPost b b' (Bytes.sha256 (sevm.data.sliceD sP.toNat 64 0)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (sig1Img img sevm sP.toNat) ∧ M'.size = 832 ∧
      ∀ r, SFunc.RunExactCut prog sevm []
          (St b' (Nat.toB256 32 :: Nat.toB256 448 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 ::
            sP :: R) M' G) t_096a_c14 r →
        SFunc.RunExactCut prog sevm []
          (St b (0x20 :: 0x160 :: 0 :: 0x80 :: a :: rt :: 96 :: sP :: R) M (G + 883))
          t_086e_c12 r := by
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
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ :=
    copy_sha_gen (fs := prog) (sevm := sevm) (C := []) (b := b) (M := M3) (G := G)
      (R := 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: R)
      (X := t_08f8_c12) (img := img3) (n := 832) (s := 384) (d := 448)
      (x1 := Nat.toB256 384) (x3 := Nat.toB256 448) (x4 := Nat.toB256 352)
      prog_14 (by simp) hwf3 hr3 hs3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) hfp3 hw1 hw2 (by simp; omega) hsha.nodeleg hsha.warm hsha.pre hsha.fork
      hdepth (by omega)
  rw [cdWord_pair] at hpost
  refine ⟨b', M', hpost, hwf', hr', by rw [hs']; rfl, fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show max 832 (448 + 96) = 832 from rfl, Nat.sub_self, Nat.add_zero] at hc
  have h352 : (0x160 : B256).toNat = 352 := rfl
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  unfold t_086e_c12
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := pkR) ?_ (by rw [h352]; exact read_word hr 352 hpk) ?_
    (by simp; omega) ?_
  · rw [h352]; exact charge_covered hs (by decide) (by decide)
  · rw [h352]; exact read_covered hs (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_dup (n := 10) rfl (by simp; omega) ?_
  refine rxc_dup (n := 12) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_callRet prog_13 (slice13 (dv := Nat.toB256 64) (av := sP) (by simp; omega)
    (by decide) (by decide) (by decide) (push0_add sP)) ?_
  unfold t_0884_c12
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 352) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs (by decide) (by decide)
  · rw [h40]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 384) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_calldatacopy (c := 9) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [St.extCost_eq hs, toNat_toB256' (by decide), toNat_toB256' (by decide),
      memExtSize_of_le (by decide) (by decide), Nat.sub_self]
    rfl
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 448) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 352) ?_ (by rw [h40]; exact read_word hr1 64 hfp1) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs1 (by decide) (by decide)
  · rw [h40]; exact read_covered hs1 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 96) (by decide) (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M2) ?_ (by rw [toNat_toB256' (by decide)]; rfl) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs1 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs2 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 448) ?_ (by rw [h40]; exact read_word hr3 64 hfp3) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs3 (by decide) (by decide)
  · rw [h40]; exact read_covered hs3 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by decide)]; exact read_word hr3 352 hlen3) ?_ (by simp; omega) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs3 (by decide) (by decide)
  · rw [toNat_toB256' (by decide)]; exact read_covered hs3 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 384) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_08bb_c12_eq]
  exact hc


/-! ## Site 2: `sha256(signature[64:] ‖ 0^32)` -/

theorem push40_add {x : B256} (h : x.toNat + 64 < 2 ^ 256) :
    Bytes.toB256 [0x40] + x = Nat.toB256 (x.toNat + 64) := by
  apply B256.toNat_inj
  rw [B256.toNat_add, show (Bytes.toB256 [0x40]).toNat = 64 from rfl, toNat_toB256' h,
    Nat.lo_eq_of_lt (by omega)]
  omega

/-- The image after site 2: the last 32 signature bytes at `0x1e0`, a zero word at `0x200`,
the length at `0x1c0`, the free pointer `0x220`, the digest at `0x220`. -/
def sig2Img (img : Bytes) (sevm : Sevm) (p : Nat) : Bytes :=
  shaImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 480
    (sevm.data.sliceD p 32 0)) 512 (0 : B256).toBytes) 448 (Nat.toB256 64).toBytes) 64
    (Nat.toB256 544).toBytes) 544 (cdWord sevm p) 0

theorem sig_site2 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP pkR h1 : B256} {R : List B256}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : R.length ≤ 20) (hG : G + 256 < 2 ^ 256)
    (hsP : sP.toNat + 96 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 448).toBytes)
    (hh1 : img.sliceD 448 32 0 = h1.toBytes) :
    ∃ b' M', ShaCallPost b b'
        (Bytes.sha256 (sevm.data.sliceD (sP.toNat + 64) 32 0 ++ (0 : B256).toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (sig2Img img sevm (sP.toNat + 64)) ∧ M'.size = 832 ∧
      ∀ r, SFunc.RunExactCut prog sevm []
          (St b' (Nat.toB256 32 :: Nat.toB256 544 :: h1 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt ::
            96 :: sP :: R) M' G) t_0a66_c15 r →
        SFunc.RunExactCut prog sevm []
          (St b (Nat.toB256 32 :: Nat.toB256 448 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 ::
            sP :: R) M (G + 892)) t_096a_c14 r := by
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
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ :=
    copy_sha_gen (fs := prog) (sevm := sevm) (C := []) (b := b) (M := M4) (G := G)
      (R := h1 :: 2 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: R)
      (X := t_09f4_c14) (img := img4) (n := 832) (s := 480) (d := 544)
      (x1 := Nat.toB256 480) (x3 := Nat.toB256 544) (x4 := Nat.toB256 448)
      prog_15 (by simp) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) hfp4 hw1 hw2 (by simp; omega) hsha.nodeleg hsha.warm hsha.pre hsha.fork
      hdepth (by omega)
  rw [cdWord_toBytes] at hpost
  refine ⟨b', M', hpost, hwf', hr', by rw [hs']; rfl, fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show max 832 (544 + 96) = 832 from rfl, Nat.sub_self, Nat.add_zero] at hc
  have h448 : (Nat.toB256 448).toNat = 448 := toNat_toB256' (by decide)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  unfold t_096a_c14
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := h1) ?_ (by rw [h448]; exact read_word hr 448 hh1) ?_
    (by simp; omega) ?_
  · rw [h448]; exact charge_covered hs (by decide) (by decide)
  · rw [h448]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 9) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 13) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_callRet prog_13 (slice13 (dv := Nat.toB256 32) (av := Nat.toB256 p)
    (by simp; omega) (by decide) (by decide) (by decide) (push40_add (by omega))) ?_
  unfold t_097b_c14
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 448) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs (by decide) (by decide)
  · rw [h40]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 480) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_calldatacopy (c := 6) ?_ (by rw [toNat_toB256' (by decide), toNat_toB256' (by omega),
    toNat_toB256' (by decide)]) ?_
  · rw [St.extCost_eq hs, toNat_toB256' (by decide), toNat_toB256' (by decide),
      memExtSize_of_le (by decide) (by decide), Nat.sub_self]
    rfl
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_add' (v := Nat.toB256 512) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M2) ?_ (by rw [toNat_toB256' (by decide)]; rfl) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs1 (by decide) (by decide)
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 448) ?_ (by rw [h40]; exact read_word hr2 64 hfp2) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by decide) (by decide)
  · rw [h40]; exact read_covered hs2 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs2 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 544) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by decide)]; exact read_word hr4 448 hlen4) ?_ (by simp; omega) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs4 (by decide) (by decide)
  · rw [toNat_toB256' (by decide)]; exact read_covered hs4 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 480) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_09b7_c14_eq]
  exact hc

/-! ## Site 3: `sha256(h₁ ‖ h₂)` -/

/-- The image after site 3: `h₁ ‖ h₂` at `0x240`, the length at `0x220`, the free pointer
`0x280`, the digest at `0x280`. -/
def sig3Img (img : Bytes) (h1 h2 : B256) : Bytes :=
  shaImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 576 h1.toBytes) 608
    h2.toBytes) 544 (Nat.toB256 64).toBytes) 64 (Nat.toB256 640).toBytes) 640 h1 h2

theorem sig_site3 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {h1 h2 : B256} {R : List B256}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : R.length ≤ 40) (hG : G + 256 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 544).toBytes)
    (hh2 : img.sliceD 544 32 0 = h2.toBytes) :
    ∃ b' M', ShaCallPost b b' (Bytes.sha256 (h1.toBytes ++ h2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (sig3Img img h1 h2) ∧ M'.size = 832 ∧
      ∀ r, SFunc.RunExactCut prog sevm []
          (St b' (Nat.toB256 32 :: Nat.toB256 640 :: R) M' G) t_0b4c_c16 r →
        SFunc.RunExactCut prog sevm []
          (St b (Nat.toB256 32 :: Nat.toB256 544 :: h1 :: 2 :: R) M (G + 751)) t_0a66_c15 r := by
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
  have hfp3 : img3.sliceD 64 32 0 = (Nat.toB256 544).toBytes := by
    rw [himg3, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), hfp2]
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
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ :=
    copy_sha_gen (fs := prog) (sevm := sevm) (C := []) (b := b) (M := M4) (G := G)
      (R := R) (X := t_0ada_c15) (img := img4) (n := 832) (s := 576) (d := 640)
      (x1 := Nat.toB256 576) (x3 := Nat.toB256 640) (x4 := Nat.toB256 544)
      prog_16 (by simp) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) hfp4 hw1 hw2 (by omega) hsha.nodeleg hsha.warm hsha.pre hsha.fork
      hdepth (by omega)
  refine ⟨b', M', hpost, hwf', hr', by rw [hs']; rfl, fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show max 832 (640 + 96) = 832 from rfl, Nat.sub_self, Nat.add_zero] at hc
  have h544 : (Nat.toB256 544).toNat = 544 := toNat_toB256' (by decide)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  unfold t_0a66_c15
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := h2) ?_ (by rw [h544]; exact read_word hr 544 hh2) ?_
    (by simp; omega) ?_
  · rw [h544]; exact charge_covered hs (by decide) (by decide)
  · rw [h544]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 544) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs (by decide) (by decide)
  · rw [h40]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 576) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_mstore (c := 3) (M' := M1) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 608) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_mstore (c := 3) (M' := M2) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs1 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 544) ?_ (by rw [h40]; exact read_word hr2 64 hfp2) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by decide) (by decide)
  · rw [h40]; exact read_covered hs2 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 0) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs2 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_add' (v := Nat.toB256 640) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by decide) (by decide)
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by decide)]; exact read_word hr4 544 hlen4) ?_ (by simp; omega) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs4 (by decide) (by decide)
  · rw [toNat_toB256' (by decide)]; exact read_covered hs4 (by decide) (by decide)
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 576) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_0a9d_c15_eq]
  exact hc

/-! ## Composition -/

theorem signatureRoot_eq (sevm : Sevm) (p : Nat) :
    BeaconDeposit.signatureRoot Bytes.sha256 (sevm.data.sliceD p 96 0) =
      Bytes.sha256 ((Bytes.sha256 (sevm.data.sliceD p 64 0)).toBytes ++
        (Bytes.sha256 (sevm.data.sliceD (p + 64) 32 0 ++ (0 : B256).toBytes)).toBytes) := by
  have h96 : sevm.data.sliceD p 96 0 = sevm.data.sliceD p 64 0 ++ sevm.data.sliceD (p + 64) 32 0 :=
    List.sliceD_add _ _ 64 p 32
  have hl : (sevm.data.sliceD p 64 0).length = 64 := List.length_sliceD _ _ _ _
  rw [BeaconDeposit.signatureRoot, h96, List.take_left' hl, List.drop_left' hl,
    show BeaconDeposit.zeros 32 = (0 : B256).toBytes by decide]
  rfl

-- SEGMENT: signatureRoot
/-- **Segment 4 (`0x086e → 0x0b4c`, trees `t_086e_c12`, loop entries 14, 15, 16, ending at
`t_0b4c_c16`).**  `pkR` is loaded from `0x160` onto the stack; then three precompile hashes,
each over 64 packed bytes built at the free pointer, copied by the count-down word loop (two
passes: first inlined, second in the loop entry), merged and `STATICCALL`ed:

* `sha256(signature[:64])` (`0x0873 … 0x096a`): the slice helper (entry 13, pc `0x16fe`,
  `callNext 13`, bounds `0 ≤ 64 ≤ 96`) returns `sP` and `64`; `CALLDATACOPY` of 64 bytes at
  `0x180`; loop `0x08bb` (entry 14); digest at `0x1c0`, loaded;
* `sha256(signature[64:] ‖ 0^32)` (`0x096d … 0x0a66`): the slice helper returns `sP + 64` and
  `32`; `CALLDATACOPY` of 32 bytes and a zero word; loop `0x09b7` (entry 15); digest at `0x220`;
* `sha256(h₁ ‖ h₂)` (`0x0a66 … 0x0b4c`): the two words stored, loop `0x0a9d` (entry 16); the
  digest `signatureRoot` at `0x280`, the new free pointer.

2526 gas; memory stays at `0x340`.

Proof sketch.  Three instances of the packed-copy + precompile shape (see segment 3); the slice
helper's two `callNext 13` runs are short straight-line walks (`rx_callRet (j := 13)`; its
`t_16fe_c13` tree has two `GT`/`JUMPI` bound checks and returns two words).  `hsP` keeps
`sP + 64` from wrapping.  The digest equation is `BeaconDeposit.signatureRoot`'s definition with
`(sliceD sP 96).take 64 = sliceD sP 64` and `(sliceD sP 96).drop 64 = sliceD (sP + 64) 32`
(`List.sliceD_split`). -/
theorem body_signatureRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR : B256} {G : Nat}
    {M : Mem}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hsP : sP.toNat + 96 < 2 ^ 256) (hG : G + 2526 < 2 ^ 256)
    (hM : BodyMem M 832 0x160
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x160, pkR.toBytes)]) :
    ∃ b' M', Keep b b' ∧
      BodyMem M' 832 0x280
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x280, (BeaconDeposit.signatureRoot Bytes.sha256
            (sevm.data.sliceD sP.toNat 96 0)).toBytes)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G)
          t_0b4c_c16 o →
        SFunc.RunExact prog sevm
          (St b [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M (G + 2526))
          t_086e_c12 o := by
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
  obtain ⟨b1, M1, hp1, hwf1, hr1, hs1, r1⟩ := sig_site1 (sevm := sevm) (b := b) (M := M)
    (img := img) (G := G + 751 + 892) (a := a) (rt := rt) (sP := sP) (pkR := pkR) (R := R)
    hsha hdepth (by simp [hR]) (by omega) hwf hr hs hfp0 hpk
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
  obtain ⟨b2, M2, hp2, hwf2, hr2, hs2, r2⟩ := sig_site2 (sevm := sevm) (b := b1) (M := M1)
    (img := I1) (G := G + 751) (a := a) (rt := rt) (sP := sP) (pkR := pkR) (h1 := h1) (R := R)
    (hsha.keep hK1) hdepth (by simp [hR]) (by omega) hsP hwf1 hr1 hs1 hI1fp hI1h
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
  obtain ⟨b3, M3, hp3, hwf3, hr3, hs3, r3⟩ := sig_site3 (sevm := sevm) (b := b2) (M := M2)
    (img := I2) (G := G) (h1 := h1) (h2 := h2)
    (R := 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: R)
    ((hsha.keep hK1).keep hK2) hdepth (by simp [hR]) (by omega) hwf2 hr2 hs2 hI2fp hI2h
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
  refine ⟨b3, M3, hK1.trans (hK2.trans hK3), ⟨hwf3, hs3, I3, hr3, ?_, ?_⟩, ?_⟩
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
  intro o k
  rw [SFunc.runExact_iff_runExactCut_nil] at k ⊢
  rw [show G + 2526 = G + 751 + 892 + 883 by omega]
  refine r1 _ (r2 _ (r3 _ ?_))
  exact k


end Blanc.Lift.BeaconDeposit
