import Blanc.Lift.BeaconDeposit.BodyNode
import Blanc.Lift.InvWalkSha

/-!
# Safety segment B5: the `DepositData` node, inverted (converse of `body_dataNode`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- **Site 1, inverted** (converse of `node_site1`). -/
private theorem inv_node1 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP wP pkR sR : B256} {R : List B256} {r : Seg}
    (hsha : ShaReady sevm b)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 640).toBytes)
    (hsR : img.sliceD 640 32 0 = sR.toBytes)
    (run : SFunc.RunCut prog sevm []
      (St b (0x20 :: 0x280 :: 0 :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R) M G)
      t_0b4c_c16 r) :
    ∃ b' M' G', ShaCallPost b b'
        (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (node1Img img sevm pkR wP.toNat) ∧ M'.size = 832 ∧
      SFunc.RunCut prog sevm []
        (St b' (Nat.toB256 32 :: Nat.toB256 736 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt ::
          96 :: sP :: 32 :: wP :: R) M' G') t_0c4b_c17 r := by
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
  have h640 : (0x280 : B256).toNat = 640 := rfl
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have t640 : (Nat.toB256 640).toNat = 640 := toNat_toB256' (by decide)
  have t672 : (Nat.toB256 672).toNat = 672 := toNat_toB256' (by decide)
  have t704 : (Nat.toB256 704).toNat = 704 := toNat_toB256' (by decide)
  unfold t_0b4c_c16 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h640, read_word hr 640 hsR, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 672) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t672, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 704) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_calldatacopy s1
  rw [t704, show (32 : B256).toNat = 32 from rfl, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 736) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr2 64 hfp2, read_covered hs2 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 96) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t640, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr4 64 hfp4, read_covered hs4 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [t640, read_word hr4 640 hlen4, read_covered hs4 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 672) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_0b9c_c16_eq] at run
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 672) (d := 736) (n := 832)
    (x1 := Nat.toB256 672) (x3 := Nat.toB256 736) (x4 := Nat.toB256 640)
    (R := 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R)
    prog_17 (by simp) (by decide) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfp4 hw1 hw2 hsha.nodeleg hsha.warm hsha.pre hsha.fork hsha.depth run
  rw [cdWord_toBytes] at hpost
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; rfl, run⟩

/-- **Site 2, inverted** (converse of `node_site2`). -/
private theorem inv_node2 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {a rt sP wP pkR sR n1 : B256} {R : List B256} {r : Seg}
    (hsha : ShaReady sevm b)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 832)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 736).toBytes)
    (hn1 : img.sliceD 736 32 0 = n1.toBytes)
    (h80 : img.sliceD 128 32 0 = (Nat.toB256 8).toBytes)
    (ha0 : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat)
    (run : SFunc.RunCut prog sevm []
      (St b (Nat.toB256 32 :: Nat.toB256 736 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt ::
        96 :: sP :: 32 :: wP :: R) M G) t_0c4b_c17 r) :
    ∃ b' M' G', ShaCallPost b b'
        (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++
          sR.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg (node2Pack img sR) 832 (amtWord a) sR) ∧
      M'.size = 928 ∧
      SFunc.RunCut prog sevm []
        (St b' (Nat.toB256 32 :: Nat.toB256 832 :: n1 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a ::
          rt :: 96 :: sP :: 32 :: wP :: R) M' G') t_0dc0_c19 r := by
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
  have h736 : (Nat.toB256 736).toNat = 736 := toNat_toB256' (by decide)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have h80' : (0x80 : B256).toNat = 128 := rfl
  have h160 : (Nat.toB256 160).toNat = 160 := toNat_toB256' (by decide)
  have h768 : (Nat.toB256 768).toNat = 768 := toNat_toB256' (by decide)
  have t776 : (Nat.toB256 776).toNat = 776 := toNat_toB256' (by decide)
  have t800 : (Nat.toB256 800).toNat = 800 := toNat_toB256' (by decide)
  unfold t_0c4b_c17 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h736, read_word hr 736 hn1, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h80', read_word hr 128 h80, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 768) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 160) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_0c6c_c17_eq] at run
  obtain ⟨_, run⟩ := ric_mcpy_exit (s := 160) (d := 768) (l := 8) (by omega) run
  unfold t_0ca9_c17 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 24) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_exp s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := maskLo)
    (by rw [show Nat.toB256 24 = (24 : B256) by decide]; rfl) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := maskTop8) not_maskLo (ri_not s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h160, read_word hr 160 hWb, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h768, read_word hr 768 hDb, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := V) (by rfl) (ri_or s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h768, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 776) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_not s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (b256_and_zero _) (ri_and s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_not s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (b256_and_zero _) (ri_and s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t776, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 800) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t800, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 832) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr3 64 hfp3, read_covered hs3 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 96) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h736, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM5] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr5 64 hfp5, read_covered hs5 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h736, read_word hr5 736 hlen5, read_covered hs5 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 768) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_0d11_c17_eq] at run
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 768) (d := 832) (n := 832)
    (x1 := Nat.toB256 768) (x3 := Nat.toB256 832) (x4 := Nat.toB256 736)
    (R := n1 :: 2 :: 0 :: sR :: pkR :: 0x80 :: a :: rt :: 96 :: sP :: 32 :: wP :: R)
    prog_19 (by simp) (by decide) hwf5 hr5 hs5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfp5 (hpack ▸ node2Pack_w1 ha0) (hpack ▸ node2Pack_w2)
    hsha.nodeleg hsha.warm hsha.pre hsha.fork hsha.depth run
  rw [amtWord_toBytes] at hpost
  exact ⟨b', M', G', hpost, hwf', hpack ▸ hr', by rw [hs']; rfl, run⟩

/-- **Site 3, inverted** (converse of `node_site3`). -/
private theorem inv_node3 {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes} {G : Nat}
    {h1 h2 : B256} {R : List B256} {r : Seg}
    (hsha : ShaReady sevm b)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 928)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 832).toBytes)
    (hh2 : img.sliceD 832 32 0 = h2.toBytes)
    (run : SFunc.RunCut prog sevm []
      (St b (Nat.toB256 32 :: Nat.toB256 832 :: h1 :: 2 :: R) M G) t_0dc0_c19 r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (h1.toBytes ++ h2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (node3Img img h1 h2) ∧ M'.size = 1024 ∧
      SFunc.RunCut prog sevm [] (St b' (Nat.toB256 32 :: Nat.toB256 928 :: R) M' G')
        t_0ea6_c20 r := by
  set img1 := Bytes.writeAt img 864 h1.toBytes with himg1
  set img2 := Bytes.writeAt img1 896 h2.toBytes with himg2
  set img3 := Bytes.writeAt img2 832 (Nat.toB256 64).toBytes with himg3
  set img4 := Bytes.writeAt img3 64 (Nat.toB256 928).toBytes with himg4
  set M1 := M.write 864 h1.toBytes with hM1
  set M2 := M1.write 896 h2.toBytes with hM2
  set M3 := M2.write 832 (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 928).toBytes with hM4
  have hs1 : M1.size = 928 := by
    rw [hM1, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; rfl
  have hs2 : M2.size = 928 := by
    rw [hM2, Mem.size_write_word_aligned (by rw [hs1]) (by decide), hs1]; rfl
  have hs3 : M3.size = 928 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2]) (by decide), hs2]; rfl
  have hs4 : M4.size = 928 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs3]) (by decide), hs3]; rfl
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 : Mem.Reads M1 img1 := hr.write hwf _ _
  have hr2 : Mem.Reads M2 img2 := hr1.write hwf1 _ _
  have hr3 : Mem.Reads M3 img3 := hr2.write hwf2 _ _
  have hr4 : Mem.Reads M4 img4 := hr3.write hwf3 _ _
  have hfp2 : img2.sliceD 64 32 0 = (Nat.toB256 832).toBytes := by
    rw [himg2, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), hfp]
  have hfp4 : img4.sliceD 64 32 0 = (Nat.toB256 928).toBytes := by
    have := Bytes.sliceD_writeAt img3 (Nat.toB256 928).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlen4 : img4.sliceD 832 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega)]
    have := Bytes.sliceD_writeAt img2 (Nat.toB256 64).toBytes 832
    rwa [B256.length_toBytes] at this
  have hw1 : img4.sliceD 864 32 0 = h1.toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg1]
    have := Bytes.sliceD_writeAt img h1.toBytes 864
    rwa [B256.length_toBytes] at this
  have hw2 : img4.sliceD (864 + 32) 32 0 = h2.toBytes := by
    rw [himg4, sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg3,
      sliceD_writeAt_out (by rw [B256.length_toBytes]; omega), himg2]
    have := Bytes.sliceD_writeAt img1 h2.toBytes 896
    rwa [B256.length_toBytes] at this
  have h832 : (Nat.toB256 832).toNat = 832 := toNat_toB256' (by decide)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have t864 : (Nat.toB256 864).toNat = 864 := toNat_toB256' (by decide)
  have t896 : (Nat.toB256 896).toNat = 896 := toNat_toB256' (by decide)
  unfold t_0dc0_c19 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h832, read_word hr 832 hh2, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 864) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t864, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 896) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [t896, ← hM2] at run
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
  rw [h832, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 928) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h832, read_word hr4 832 hlen4, read_covered hs4 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 864) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [t_0df7_c19_eq] at run
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 864) (d := 928) (n := 928)
    (x1 := Nat.toB256 864) (x3 := Nat.toB256 928) (x4 := Nat.toB256 832) (R := R)
    prog_20 (by simp) (by decide) hwf4 hr4 hs4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfp4 hw1 hw2 hsha.nodeleg hsha.warm hsha.pre hsha.fork hsha.depth run
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; rfl, run⟩

-- SEGMENT: safeDataNode
/-- **Inversion of segment 5 (`t_0b4c_c16 → t_0ea6_c20`).**

Proof sketch.  Three instances of the inverted precompile block (segment B3's sketch); the
amount copy (`mload 0x80 = 8`: the count-down loop makes no pass, the merge keeps the top 8
bytes of `le64 a`) as in `body_dataNode`. -/
theorem safe_dataNode {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR : B256} {G : Nat}
    {M : Mem} {o : Outcome}
    (hsha : ShaReady sevm b)
    (hM : BodyMem M 832 0x280
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x280, sR.toBytes)])
    (run : SFunc.Run prog sevm
      (St b [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M G)
      t_0b4c_c16 o) :
    ∃ b' M' G', Keep b b' ∧
      BodyMem M' 1024 0x3a0
        [(0x3a0, (BeaconDeposit.hashPair Bytes.sha256
          (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0))
          (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++
            sR.toBytes))).toBytes)] ∧
      SFunc.Run prog sevm
        (St b' [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G')
        t_0ea6_c20 o := by
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
  obtain ⟨b1, M1, G1, hp1, hwf1, hr1, hs1, run⟩ :=
    inv_node1 (a := a) (rt := rt) (sP := sP) (R := R) hsha hwf hr hs hfp0 hsR run.cut
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
  obtain ⟨b2, M2, G2, hp2, hwf2, hr2, hs2, run⟩ :=
    inv_node2 (hsha.keep hK1) hwf1 hr1 hs1 hI1fp hI1n
      ((hI1 128 32 (by omega) (by omega)).trans h80)
      ((hI1 160 8 (by omega) (by omega)).trans ha0) run
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
  obtain ⟨b3, M3, G3, hp3, hwf3, hr3, hs3, run⟩ :=
    inv_node3 ((hsha.keep hK1).keep hK2) hwf2 hr2 hs2 hI2fp hI2n run
  have hK3 := Keep.of_sha hp3
  refine ⟨b3, M3, G3, hK1.trans (hK2.trans hK3), ⟨hwf3, hs3, node3Img I2 n1 n2, hr3, ?_, ?_⟩,
    run.uncut⟩
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

end Blanc.Lift.BeaconDeposit
