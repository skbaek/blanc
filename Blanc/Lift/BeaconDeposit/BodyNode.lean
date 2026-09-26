import Blanc.Lift.BeaconDeposit.BodyShaKit

/-!
# Body segment 5: the `DepositData` node

From `0x0b4c` (tree `t_0b4c_c16`, `signature_root` in memory) through the three hashes of
`node` to the return-size check's continuation at `0x0ea6` (tree `t_0ea6_c20`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## Site 1: `sha256(pubkey_root ‖ withdrawal_credentials)` -/

/-- The image after site 1: `pkR ‖ wc` at `0x2a0`, the length at `0x280`, the free pointer
`0x2e0`, the digest at `0x2e0`. -/
def node1Img (img : Bytes) (sevm : Sevm) (pkR : B256) (wp : Nat) : Bytes :=
  shaImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 672 pkR.toBytes) 704
    (sevm.data.sliceD wp 32 0)) 640 (Nat.toB256 64).toBytes) 64 (Nat.toB256 736).toBytes) 736
    pkR (cdWord sevm wp)

theorem node_site1 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP wP pkR sR : B256} {R : List B256}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : R.length ≤ 20) (hG : G + 256 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 640).toBytes)
    (hsR : img.sliceD 640 32 0 = sR.toBytes) :
    ∃ b' M', ShaCallPost b b'
        (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (node1Img img sevm pkR wP.toNat) ∧ M'.size = 832 ∧
      ∀ r, SFunc.RunExactCut prog sevm []
          (St b' (Nat.toB256 32 :: Nat.toB256 736 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt ::
            96 :: sP :: 32 :: wP :: R) M' G) t_0c4b_c17 r →
        SFunc.RunExactCut prog sevm []
          (St b (0x20 :: 0x280 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R) M
            (G + 803)) t_0b4c_c16 r := by
  set img1 := Bytes.writeAt img 672 pkR.toBytes with himg1
  set img2 := Bytes.writeAt img1 704 (sevm.data.sliceD wP.toNat 32 0) with himg2
  set img3 := Bytes.writeAt img2 640 (Nat.toB256 64).toBytes with himg3
  set img4 := Bytes.writeAt img3 64 (Nat.toB256 736).toBytes with himg4
  set M1 := M.write 672 pkR.toBytes with hM1
  set M2 := M1.write 704 (sevm.data.sliceD wP.toNat 32 0) with hM2
  set M3 := M2.write 640 (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 736).toBytes with hM4
  have hs1 : M1.size = 832 := by
    rw [hM1, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; rfl
  have hs2 : M2.size = 832 := by
    rw [hM2, Mem.size_write_of_le (by rw [List.length_sliceD, hs1]; decide), hs1]
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
  have hfp2 : img2.sliceD 64 32 0 = (Nat.toB256 640).toBytes := by
    rw [himg2, sliceD_writeAt_out (by rw [List.length_sliceD]; omega), himg1,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), hfp]
  have hfp4 : img4.sliceD 64 32 0 = (Nat.toB256 736).toBytes := by
    have := Bytes.sliceD_writeAt img3 (Nat.toB256 736).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlen4 : img4.sliceD 640 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
    have := Bytes.sliceD_writeAt img2 (Nat.toB256 64).toBytes 640
    rwa [B256.length_toBytes] at this
  have hw1 : img4.sliceD 672 32 0 = pkR.toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [List.length_sliceD]; omega), himg1]
    have := Bytes.sliceD_writeAt img pkR.toBytes 672
    rwa [B256.length_toBytes] at this
  have hw2 : img4.sliceD (672 + 32) 32 0 = (cdWord sevm wP.toNat).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2]
    simpa using sliceD_cd_word img1 sevm 704 wP.toNat 32 0 (by omega)
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ :=
    copy_sha_gen (fs := prog) (sevm := sevm) (C := []) (b := b) (M := M4) (G := G)
      (R := 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R)
      (X := t_0bd9_c16) (img := img4) (n := 832) (s := 672) (d := 736)
      (x1 := Nat.toB256 672) (x3 := Nat.toB256 736) (x4 := Nat.toB256 640)
      prog_17 (by simp) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) hfp4 hw1 hw2 (by simp; omega) hsha.nodeleg hsha.warm hsha.pre hsha.fork
      hdepth (by omega)
  rw [cdWord_toBytes] at hpost
  refine ⟨b', M', hpost, hwf', hr', by rw [hs']; rfl, fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show max 832 (736 + 96) = 832 from rfl, Nat.sub_self, Nat.add_zero] at hc
  have h640 : (0x280 : B256).toNat = 640 := rfl
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  unfold t_0b4c_c16
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := sR) ?_ (by rw [h640]; exact read_word hr 640 hsR) ?_
    (by simp; omega) ?_
  · rw [h640]; exact charge_covered hs (by decide) (by decide)
  · rw [h640]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 640) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs (by decide) (by decide)
  · rw [h40]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 672) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 5) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M1) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs (by decide) (by decide)
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 7) rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 15) rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 15) rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_add' (v := Nat.toB256 704) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_calldatacopy (c := 6) (M' := M2) ?_ (by rw [toNat_toB256' (by decide)]; try rfl) ?_
  · rw [St.extCost_eq hs1, toNat_toB256' (by decide), show (32 : B256).toNat = 32 from rfl,
      memExtSize_of_le (by decide) (by decide), Nat.sub_self]
    rfl
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 736) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 640) ?_ (by rw [h40]; exact read_word hr2 64 hfp2) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by decide) (by decide)
  · rw [h40]; exact read_covered hs2 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 96) (by decide) (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs2 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 736) ?_ (by rw [h40]; exact read_word hr4 64 hfp4) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs4 (by decide) (by decide)
  · rw [h40]; exact read_covered hs4 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by decide)]; exact read_word hr4 640 hlen4) ?_ (by simp; omega) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs4 (by decide) (by decide)
  · rw [toNat_toB256' (by decide)]; exact read_covered hs4 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 672) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_0b9c_c16_eq]
  exact hc


/-! ## Site 2: `sha256(amount ‖ 0^24 ‖ signature_root)` -/

/-- The partial-word mask `256^24 - 1` (the low 24 bytes). -/
def maskLo : B256 := B256.bexp (Bytes.toB256 [0x01, 0x00]) 24 - Bytes.toB256 [0x01]

theorem maskLo_eq : maskLo =
    ((((0 : UInt64), (0xffffffffffffffff : UInt64)) : B128),
      (((0xffffffffffffffff : UInt64), (0xffffffffffffffff : UInt64)) : B128)) := by
  apply B256.toNat_inj
  decide +kernel

theorem not_maskLo : (~~~ maskLo) = maskTop8 := rfl

theorem uint64_and_max (x : UInt64) : x &&& (0xffffffffffffffff : UInt64) = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt64.toNat_lt x)]

/-- The merge keeps the top eight bytes of the source word. -/
theorem merge8 (W D : B256) :
    ((W &&& maskTop8) ||| (D &&& maskLo)).toBytes.take 8 = W.toBytes.take 8 := by
  rw [maskTop8_eq, maskLo_eq]
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := W
  obtain ⟨⟨e, f⟩, ⟨g, h⟩⟩ := D
  change List.take 8 (B256.toBytes (B256.or (B256.and _ _) (B256.and _ _))) = _
  simp only [B256.or, B256.and, B256.toBytes, B128.toBytes]
  change ((B128.or (B128.and _ _) (B128.and _ _)).1.toBytes ++ _ ++ _).take 8 =
    (a.toBytes ++ _ ++ _).take 8
  simp only [B128.or, B128.and, uint64_and_max, UInt64.and_zero, UInt64.or_zero,
    List.append_assoc]
  rw [List.take_left' (UInt64.length_toBytes a), List.take_left' (UInt64.length_toBytes a)]

/-- The amount word as the site hashes it: `le64 a ‖ 0^24`. -/
def amtWord (a : B256) : B256 := Bytes.toB256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24)

theorem amtWord_toBytes (a : B256) :
    (amtWord a).toBytes = BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 :=
  Bytes.toBytes_toB256_of_length rfl

/-- The merged word stored at `0x300`. -/
def mergedWord (img : Bytes) : B256 :=
  (Bytes.toB256 (img.sliceD 160 32 0) &&& maskTop8) |||
    (Bytes.toB256 (img.sliceD 768 32 0) &&& maskLo)

/-- The image after the packing of site 2 (before the copy). -/
def node2Pack (img : Bytes) (sR : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 768
    (mergedWord img).toBytes) 776 (0 : B256).toBytes) 800 sR.toBytes) 736
    (Nat.toB256 64).toBytes) 64 (Nat.toB256 832).toBytes

theorem node2Pack_w1 {img : Bytes} {sR a : B256}
    (ha : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat) :
    (node2Pack img sR).sliceD 768 32 0 = (amtWord a).toBytes := by
  have hV : (mergedWord img).toBytes.take 8 = BeaconDeposit.le64 a.toNat := by
    rw [mergedWord, merge8, Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _),
      show (32 : Nat) = 8 + 24 from rfl, List.sliceD_add,
      List.take_left' (List.length_sliceD _ _ _ _), ha]
  unfold node2Pack
  rw [sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    show (32 : Nat) = 8 + 24 from rfl, List.sliceD_add,
    sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
    amtWord_toBytes, ← hV]
  have hl : (mergedWord img).toBytes.length = 32 := B256.length_toBytes _
  congr 1

theorem node2Pack_w2 {img : Bytes} {sR : B256} :
    (node2Pack img sR).sliceD (768 + 32) 32 0 = sR.toBytes := by
  unfold node2Pack
  rw [sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
    sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
  have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt img 768
    (mergedWord img).toBytes) 776 (0 : B256).toBytes) sR.toBytes 800
  rwa [B256.length_toBytes] at this

theorem node_site2 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP wP pkR sR n1 : B256} {R : List B256}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : R.length ≤ 20) (hG : G + 256 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 736).toBytes)
    (hn1 : img.sliceD 736 32 0 = n1.toBytes)
    (h80 : img.sliceD 128 32 0 = (Nat.toB256 8).toBytes)
    (ha0 : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat) :
    ∃ b' M', ShaCallPost b b'
        (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++
          sR.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg (node2Pack img sR) 832 (amtWord a) sR) ∧
      M'.size = 928 ∧
      ∀ r, SFunc.RunExactCut prog sevm []
          (St b' (Nat.toB256 32 :: Nat.toB256 832 :: n1 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a ::
            rt :: 96 :: sP :: 32 :: wP :: R) M' G) t_0dc0_c19 r →
        SFunc.RunExactCut prog sevm []
          (St b (Nat.toB256 32 :: Nat.toB256 736 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt ::
            96 :: sP :: 32 :: wP :: R) M (G + 989)) t_0c4b_c17 r := by
  set W := Bytes.toB256 (img.sliceD 160 32 0) with hW
  set D := Bytes.toB256 (img.sliceD 768 32 0) with hD
  set V := mergedWord img with hV
  set img1 := Bytes.writeAt img 768 V.toBytes with himg1
  set img2 := Bytes.writeAt img1 776 (0 : B256).toBytes with himg2
  set img3 := Bytes.writeAt img2 800 sR.toBytes with himg3
  set img4 := Bytes.writeAt img3 736 (Nat.toB256 64).toBytes with himg4
  set img5 := Bytes.writeAt img4 64 (Nat.toB256 832).toBytes with himg5
  set M1 := M.write 768 V.toBytes with hM1
  set M2 := M1.write 776 (0 : B256).toBytes with hM2
  set M3 := M2.write 800 sR.toBytes with hM3
  set M4 := M3.write 736 (Nat.toB256 64).toBytes with hM4
  set M5 := M4.write 64 (Nat.toB256 832).toBytes with hM5
  have hs1 : M1.size = 832 := by
    rw [hM1, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; rfl
  have hs2 : M2.size = 832 := by
    rw [hM2, Mem.size_write_word_at, hs1]; rfl
  have hs3 : M3.size = 832 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2]) (by decide), hs2]; rfl
  have hs4 : M4.size = 832 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs3]) (by decide), hs3]; rfl
  have hs5 : M5.size = 832 := by
    rw [hM5, Mem.size_write_word_aligned (by rw [hs4]) (by decide), hs4]; rfl
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hwf5 : Mem.Wf M5 := hwf4.write _ _
  have hr1 : Mem.Reads M1 img1 := hr.write hwf _ _
  have hr2 : Mem.Reads M2 img2 := hr1.write hwf1 _ _
  have hr3 : Mem.Reads M3 img3 := hr2.write hwf2 _ _
  have hr4 : Mem.Reads M4 img4 := hr3.write hwf3 _ _
  have hr5 : Mem.Reads M5 img5 := hr4.write hwf4 _ _
  have hpack : img5 = node2Pack img sR := rfl
  have hfp3 : img3.sliceD 64 32 0 = (Nat.toB256 736).toBytes := by
    rw [himg3, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), hfp]
  have hfp5 : img5.sliceD 64 32 0 = (Nat.toB256 832).toBytes := by
    have := Bytes.sliceD_writeAt img4 (Nat.toB256 832).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlen5 : img5.sliceD 736 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg5, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
    have := Bytes.sliceD_writeAt img3 (Nat.toB256 64).toBytes 736
    rwa [B256.length_toBytes] at this
  have hWb : img.sliceD 160 32 0 = W.toBytes :=
    (Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)).symm
  have hDb : img.sliceD 768 32 0 = D.toBytes :=
    (Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)).symm
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ :=
    copy_sha_gen (fs := prog) (sevm := sevm) (C := []) (b := b) (M := M5) (G := G)
      (R := n1 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R)
      (X := t_0d4e_c17) (img := img5) (n := 832) (s := 768) (d := 832)
      (x1 := Nat.toB256 768) (x3 := Nat.toB256 832) (x4 := Nat.toB256 736)
      prog_19 (by simp) hwf5 hr5 hs5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) hfp5 (hpack ▸ node2Pack_w1 ha0) (hpack ▸ node2Pack_w2) (by simp; omega)
      hsha.nodeleg hsha.warm hsha.pre hsha.fork hdepth (by omega)
  rw [amtWord_toBytes] at hpost
  refine ⟨b', M', hpost, hwf', hr', by rw [hs']; rfl, fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show calculateMemoryGasCost (max 832 (832 + 96)) - calculateMemoryGasCost 832 = 9 from
    rfl] at hc
  have h736 : (Nat.toB256 736).toNat = 736 := toNat_toB256' (by decide)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have h80' : (0x80 : B256).toNat = 128 := rfl
  have h160 : (Nat.toB256 160).toNat = 160 := toNat_toB256' (by decide)
  have h768 : (Nat.toB256 768).toNat = 768 := toNat_toB256' (by decide)
  rw [show G + 989 = G + (598 + 9) + 275 + 23 + 84 by omega]
  unfold t_0c4b_c17
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := n1) ?_ (by rw [h736]; exact read_word hr 736 hn1) ?_
    (by simp; omega) ?_
  · rw [h736]; exact charge_covered hs (by decide) (by decide)
  · rw [h736]; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 736) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs (by decide) (by decide)
  · rw [h40]; exact read_covered hs (by decide) (by decide)
  refine rxc_dup (n := 6) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 8) ?_ (by rw [h80']; exact read_word hr 128 h80) ?_
    (by simp; omega) ?_
  · rw [h80']; exact charge_covered hs (by decide) (by decide)
  · rw [h80']; exact read_covered hs (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 8) rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 8) rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 768) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 6) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 160) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_0c6c_c17_eq]
  refine mcpy_exit (s := 160) (d := 768) (l := 8) (by omega) (by simp; omega) ?_
  unfold t_0ca9_c17
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 24) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_exp' (c := 60) (by decide) (by simp; omega) ?_
  refine rxc_sub' (v := maskLo) (by rw [show Nat.toB256 24 = (24 : B256) by decide]; rfl)
    (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_not (v := maskTop8) not_maskLo (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := W) ?_ (by rw [h160]; exact read_word hr 160 hWb) ?_
    (by simp; omega) ?_
  · rw [h160]; exact charge_covered hs (by decide) (by decide)
  · rw [h160]; exact read_covered hs (by decide) (by decide)
  refine rxc_and rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := D) ?_ (by rw [h768]; exact read_word hr 768 hDb) ?_
    (by simp; omega) ?_
  · rw [h768]; exact charge_covered hs (by decide) (by decide)
  · rw [h768]; exact read_covered hs (by decide) (by decide)
  refine rxc_and rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_or (v := V) rfl (by simp; omega) ?_
  refine rxc_dup (n := 5) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M1) ?_ (by rw [h768]) ?_
  · rw [h768]; exact charge_covered hs (by decide) (by decide)
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_pop ?_
  refine rxc_add' (v := Nat.toB256 776) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_not rfl (by simp; omega) ?_
  refine rxc_and (b256_and_zero _) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_not rfl (by simp; omega) ?_
  refine rxc_and (b256_and_zero _) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M2) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs1 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 800) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by decide)]) ?_
  · rw [toNat_toB256' (by decide)]; exact charge_covered hs2 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 832) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 736) ?_ (by rw [h40]; exact read_word hr3 64 hfp3) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs3 (by decide) (by decide)
  · rw [h40]; exact read_covered hs3 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 96) (by decide) (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h736]) ?_
  · rw [h736]; exact charge_covered hs3 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M5) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs4 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 832) ?_ (by rw [h40]; exact read_word hr5 64 hfp5) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs5 (by decide) (by decide)
  · rw [h40]; exact read_covered hs5 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [h736]; exact read_word hr5 736 hlen5) ?_ (by simp; omega) ?_
  · rw [h736]; exact charge_covered hs5 (by decide) (by decide)
  · rw [h736]; exact read_covered hs5 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 768) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_0d11_c17_eq]
  exact hc

/-! ## Site 3: `sha256(left ‖ right)` -/

/-- The image after site 3: `left ‖ right` at `0x360`, the length at `0x340`, the free
pointer `0x3a0`, the digest at `0x3a0`. -/
def node3Img (img : Bytes) (h1 h2 : B256) : Bytes :=
  shaImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 864 h1.toBytes) 896
    h2.toBytes) 832 (Nat.toB256 64).toBytes) 64 (Nat.toB256 928).toBytes) 928 h1 h2

theorem node_site3 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {h1 h2 : B256} {R : List B256}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : R.length ≤ 40) (hG : G + 256 < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 928)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 832).toBytes)
    (hh2 : img.sliceD 832 32 0 = h2.toBytes) :
    ∃ b' M', ShaCallPost b b' (Bytes.sha256 (h1.toBytes ++ h2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (node3Img img h1 h2) ∧ M'.size = 1024 ∧
      ∀ r, SFunc.RunExactCut prog sevm []
          (St b' (Nat.toB256 32 :: Nat.toB256 928 :: R) M' G) t_0ea6_c20 r →
        SFunc.RunExactCut prog sevm []
          (St b (Nat.toB256 32 :: Nat.toB256 832 :: h1 :: 2 :: R) M (G + 761)) t_0dc0_c19 r := by
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ :=
    pair_mem_sha (fs := prog) (sevm := sevm) (C := []) (b := b) (M := M) (G := G) (R := R)
      (X := t_0e34_c19) (img := img) (n := 928) (f := 832) prog_20 (by simp) hwf hr hs (by decide)
      (by decide) (by decide) (by decide) (by decide) hfp hh2 (by omega) hsha.nodeleg hsha.warm
      hsha.pre hsha.fork hdepth (by omega)
  refine ⟨b', M', hpost, hwf', hr', by rw [hs']; rfl, fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show calculateMemoryGasCost (max 928 (832 + 192)) - calculateMemoryGasCost 928 = 10 from
    rfl] at hc
  rw [show t_0dc0_c19 = pairMemTree t_0df7_c19 from rfl, t_0df7_c19_eq]
  exact hc

-- SEGMENT: dataNode
/-- **Segment 5 (`0x0b4c → 0x0ea6`, trees `t_0b4c_c16`, loop entries 17, 19, 20, ending at
`t_0ea6_c20`).**  `sR` is loaded from `0x280`; then three precompile hashes over 64 packed bytes
each:

* `sha256(pkR ‖ withdrawal_credentials)` (`0x0b4c … 0x0c4b`): `pkR` stored, `CALLDATACOPY` of
  32 bytes from `wP`; loop `0x0b9c` (entry 17); digest at `0x2e0`;
* `sha256(amount ‖ 0^24 ‖ sR)` (`0x0c4b … 0x0dc0`): the amount's 8 bytes copied from its buffer
  (`mload 0x80 = 8`, the word loop `0x0c6c` makes no pass and stays in entry 17's copy, the
  partial word merged under the mask `256^24 - 1`), a zero word at `+8`, `sR` at `+32`;
  loop `0x0d11` (entry 19); digest at `0x340` (memory grows to `0x3a0`);
* `sha256(left ‖ right)` (`0x0dc0 … 0x0ea6`): loop `0x0df7` (entry 20); digest at `0x3a0`, the
  new free pointer (memory grows to `0x400`).

2553 gas.

Proof sketch.  Three instances of the packed-copy + precompile shape (segment 3).  The amount
copy is the only irregular piece: the count-down loop exits at once (`8 < 32`), and the merge
keeps the top 8 bytes of the source word (`le64 a`) and the low 24 of the destination, which the
following `MSTORE` of `0` at `+8` overwrites.  The digest equation is `hashPair` of the two inner
digests (`BeaconDeposit.hashPair`). -/
theorem body_dataNode {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR : B256} {G : Nat}
    {M : Mem}
    (hsha : ShaReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hG : G + 2553 < 2 ^ 256)
    (hM : BodyMem M 832 0x280
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x280, sR.toBytes)]) :
    ∃ b' M', Keep b b' ∧
      BodyMem M' 1024 0x3a0
        [(0x3a0, (BeaconDeposit.hashPair Bytes.sha256
          (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0))
          (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++
            sR.toBytes))).toBytes)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G)
          t_0ea6_c20 o →
        SFunc.RunExact prog sevm
          (St b [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M
            (G + 2553)) t_0b4c_c16 o := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  have hfp0 : img.sliceD 64 32 0 = (Nat.toB256 640).toBytes := by
    rw [hfp]; rfl
  have hsR : img.sliceD 640 32 0 = sR.toBytes := by
    have := hf (0x280, sR.toBytes) (by simp)
    rwa [B256.length_toBytes] at this
  have h80 : img.sliceD 128 32 0 = (Nat.toB256 8).toBytes := by
    have := hf (0x80, (8 : B256).toBytes) (by simp)
    rw [B256.length_toBytes] at this
    rw [this]; rfl
  have ha0 : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat :=
    hf (0xa0, BeaconDeposit.le64 a.toNat) (by simp)
  set R := [(48 : B256), pP, 0x01b8, sel] with hR
  -- site 1
  obtain ⟨b1, M1, hp1, hwf1, hr1, hs1, r1⟩ := node_site1 (sevm := sevm) (b := b) (M := M)
    (img := img) (G := G + 761 + 989) (a := a) (rt := rt) (sP := sP) (wP := wP) (pkR := pkR)
    (sR := sR) (R := R) hsha hdepth (by simp [hR]) (by omega) hwf hr hs hfp0 hsR
  set I1 := node1Img img sevm pkR wP.toNat
  set n1 := Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0)
  have hK1 := Keep.of_sha hp1
  have hI1 : ∀ st len, 96 ≤ st → st + len ≤ 640 → I1.sliceD st len 0 = img.sliceD st len 0 := by
    intro st len h1' h2'
    simp only [I1, node1Img]
    rw [shaImg_out (by omega), sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega),
      sliceD_writeAt_out (by rw [List.length_sliceD]; omega),
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
  have hI1fp : I1.sliceD 64 32 0 = (Nat.toB256 736).toBytes := by
    simp only [I1, node1Img]
    rw [shaImg_out (by omega)]
    have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 672
      pkR.toBytes) 704 (sevm.data.sliceD wP.toNat 32 0)) 640 (Nat.toB256 64).toBytes)
      (Nat.toB256 736).toBytes 64
    rwa [B256.length_toBytes] at this
  have hI1n : I1.sliceD 736 32 0 = n1.toBytes := by
    simp only [I1, node1Img]
    rw [shaImg_digest, cdWord_toBytes]
  -- site 2
  obtain ⟨b2, M2, hp2, hwf2, hr2, hs2, r2⟩ := node_site2 (sevm := sevm) (b := b1) (M := M1)
    (img := I1) (G := G + 761) (a := a) (rt := rt) (sP := sP) (wP := wP) (pkR := pkR)
    (sR := sR) (n1 := n1) (R := R) (hsha.keep hK1) hdepth (by simp [hR]) (by omega) hwf1 hr1 hs1
    hI1fp hI1n ((hI1 128 32 (by omega) (by omega)).trans h80)
    ((hI1 160 8 (by omega) (by omega)).trans ha0)
  set I2 := shaImg (node2Pack I1 sR) 832 (amtWord a) sR
  set n2 := Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++ sR.toBytes)
  have hK2 := Keep.of_sha hp2
  have hI2fp : I2.sliceD 64 32 0 = (Nat.toB256 832).toBytes := by
    simp only [I2, node2Pack]
    rw [shaImg_out (by omega)]
    have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt I1
      768 (mergedWord I1).toBytes) 776 (0 : B256).toBytes) 800 sR.toBytes) 736
      (Nat.toB256 64).toBytes) (Nat.toB256 832).toBytes 64
    rwa [B256.length_toBytes] at this
  have hI2n : I2.sliceD 832 32 0 = n2.toBytes := by
    simp only [I2]
    rw [shaImg_digest, amtWord_toBytes]
  -- site 3
  obtain ⟨b3, M3, hp3, hwf3, hr3, hs3, r3⟩ := node_site3 (sevm := sevm) (b := b2) (M := M2)
    (img := I2) (G := G) (h1 := n1) (h2 := n2)
    (R := 0 :: sR :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R)
    ((hsha.keep hK1).keep hK2) hdepth (by simp [hR]) (by omega) hwf2 hr2 hs2 hI2fp hI2n
  have hK3 := Keep.of_sha hp3
  refine ⟨b3, M3, hK1.trans (hK2.trans hK3), ⟨hwf3, hs3, node3Img I2 n1 n2, hr3, ?_, ?_⟩, ?_⟩
  · simp only [node3Img]
    rw [shaImg_out (by omega)]
    have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt I2 864
      n1.toBytes) 896 n2.toBytes) 832 (Nat.toB256 64).toBytes) (Nat.toB256 928).toBytes 64
    rw [B256.length_toBytes] at this
    rw [this]; rfl
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    rw [B256.length_toBytes]
    simp only [node3Img]
    rw [shaImg_digest]
    rfl
  intro o k
  rw [SFunc.runExact_iff_runExactCut_nil] at k ⊢
  rw [show G + 2553 = G + 761 + 989 + 803 by omega]
  refine r1 _ (r2 _ (r3 _ ?_))
  exact k


end Blanc.Lift.BeaconDeposit
