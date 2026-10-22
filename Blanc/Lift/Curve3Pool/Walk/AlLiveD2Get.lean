import Blanc.Lift.Curve3Pool.Walk.AlLiveD2

/-!
# `add_liquidity`, forward: `D2`

`rx_al_d2` (the fee loop's exit `t_163a_c69` or `t_163a_c93`, memory `0xaa0` →
`t_170b_c1339`): the save of `[0x140, 0xa40)` (counter `0xaa0`),
`D2 = get_D_mem(new_balances, amp)` (`getDMem_exact` over a memory of `0xb40`), the restore,
and `D2` at `0xa20`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alIdx5 : List Nat := [94, 114, 135, 157, 179, 199, 217, 231, 245, 260, 275, 290, 305, 320, 335,
  350, 365, 380, 395, 410, 424, 438, 452, 466, 480, 496, 510, 524, 540, 553, 566, 577, 588, 598,
  608, 618, 628, 638, 648, 658, 668, 678, 687, 696, 705, 714, 723, 732, 741, 750, 760, 770, 779,
  788, 797, 806, 815, 824, 833, 842, 851, 860, 869, 878, 887, 896, 905, 914, 923, 931, 939]

def alIdx6 : List Nat := [947, 955, 963, 971, 979, 987, 995, 1003, 1011, 1019, 1027, 1035, 1043,
  1052, 1060, 1068, 1075, 1082, 1089, 1096, 1103, 1110, 1117, 1124, 1131, 1138, 1145, 1152, 1159,
  1166, 1173, 1179, 1184, 1189, 1194, 1199, 1204, 1209, 1214, 1219, 1224, 1229, 1234, 1239, 1244,
  1249, 1254, 1259, 1264, 1269, 1274, 1278, 1282, 1285, 1288, 1291, 1294, 1297, 1300, 1303, 1306,
  1309, 1312, 1315, 1318, 1321, 1324, 1327, 1330, 1333, 1336]

theorem al_sv5_chain : ∀ n, n < 71 → cert.prog[alIdx5.getD n 0]? =
    some (svItL 0x0a 0xa0 0x0a 0x40 0x16 0x66 (lpBr 71 alIdx5 0x16 0x44 t_1666_c939 (n + 1))) := by
  decide +kernel

theorem al_rs5_first :
    t_16b3_c939 = rsIt 0x0a 0xa0 0x16 0xd6 (lpBr 71 alIdx6 0x16 0xb3 t_16d6_c1336 0) := rfl

theorem al_rs5_chain : ∀ n, n < 71 → cert.prog[alIdx6.getD n 0]? =
    some (rsIt 0x0a 0xa0 0x16 0xd6 (lpBr 71 alIdx6 0x16 0xb3 t_16d6_c1336 (n + 1))) := by
  decide +kernel

theorem al_prog_1339 : cert.prog[1339]? = some t_170b_c1339 := by decide +kernel

/-- The fee loop's exit before the save: drop the loop words, set the save counter. -/
def alD2Pre (f : SFunc) : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x01, 0x40] (by decide))
    (.next (.push [0x0a, 0xa0] (by decide)) (.next (.reg .mstore) f)))))

theorem al_d2_c69 : t_163a_c69 =
    alD2Pre (svItL 0x0a 0xa0 0x0a 0x40 0x16 0x66 (lpBr 71 alIdx5 0x16 0x44 t_1666_c939 0)) := rfl

theorem al_d2_c93 : t_163a_c93 =
    alD2Pre (svItL 0x0a 0xa0 0x0a 0x40 0x16 0x66 (lpBr 71 alIdx5 0x16 0x44 t_1666_c939 0)) := rfl

/-- **`D2`'s memory, exact**: the save counter at `0xaa0`, the save of `[0x140, 0xa40)`,
`get_D_mem`'s arguments at `0xac0 … 0xb20`, `get_D_mem`'s memory, `D2` parked at `0xb80` (a
growing store, so the memory is again literal), the restore counter, the restore, `D2` at
`0xa20`. -/
def alD2Mem (M : Mem) (x0 x1 x2 A : B256) (x : V3) (v : Nat) : Mem :=
  let M1 := M.write 2720 (Bytes.toB256 [1, 64]).toBytes
  let M5 := ((((saveMem M1 2720 320 72).write 2752 x0.toBytes).write 2784 x1.toBytes).write 2816
    x2.toBytes).write 2848 A.toBytes
  (restoreMem 2720 (((getDMemNext M5 (Nat.toB256 (5793 + 6)) x0 x1 x2 A x v).write 2944
    (Nat.toB256 v).toBytes).write 2720 (Bytes.toB256 [10, 32]).toBytes) (320 + 32 * 71)
    (exSaved (memWord M1) 320 72)).write 2592 (Nat.toB256 v).toBytes

theorem alD2Mem_eq {Mq0 Mq1 M1 Mq2 Mq3 Mq4 Mq5 M2 Mq6 Mq7 M3 M : Mem} {img1 : Bytes}
    {x0 x1 x2 A : B256} {x : V3} {v : Nat}
    (h0 : Mq1 = Mq0.write 2720 (Bytes.toB256 [1, 64]).toBytes) (hR1 : Mem.Reads Mq1 img1)
    (hsv : M1 = saveMem Mq1 2720 (320 + 32 * 0) (71 + 1))
    (h1 : Mq2 = M1.write 2752 x0.toBytes) (h2 : Mq3 = Mq2.write 2784 x1.toBytes)
    (h3 : Mq4 = Mq3.write 2816 x2.toBytes) (h4 : Mq5 = Mq4.write 2848 A.toBytes)
    (hg : Mem.EqExcept M2 (getDMemNext Mq5 (Nat.toB256 (5793 + 6)) x0 x1 x2 A x v) fun _ => False)
    (hs2 : M2.size = 2880)
    (h5 : Mq6 = M2.write 2944 (Nat.toB256 v).toBytes)
    (h6 : Mq7 = Mq6.write 2720 (Bytes.toB256 [10, 32]).toBytes)
    (hrs : M3 = restoreMem 2720 Mq7 (320 + 32 * 71)
      (exSaved (fun o => Bytes.toB256 (img1.sliceD o 32 0)) 320 (71 + 1)))
    (h7 : M = M3.write 2592 (Nat.toB256 v).toBytes) :
    M = alD2Mem Mq0 x0 x1 x2 A x v := by
  rw [al_saved_memWord hR1] at hrs
  rw [eqB_write_word_grow hg _ (by rw [hs2]; decide)] at h5
  rw [h7, hrs, h6, h5, h4, h3, h2, h1, hsv, h0]
  rfl

/-- **`D2`, forward, exact** (core of `rx_al_d2`). -/
theorem rx_al_d2E {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R v : Nat} {Q : Outcome → Prop} {x : V3} {A x0 x1 x2 : B256} {X : SFunc}
    (hctx : X = t_163a_c69 ∨ X = t_163a_c93)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xaa0)
    (hA : WordAt img 0x1e0 A) (hx0 : WordAt img 0x460 x0) (hx1 : WordAt img 0x480 x1)
    (hx2 : WordAt img 0x4a0 x2)
    (hX : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some x)
    (hres : getDChk x.get A.toNat 1 = some v)
    (hG : R + costGetDMem x A.toNat + 15000 ≤ G) (hroom : S.length + 150 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xba0 →
      (∀ j, j < 71 → ∀ w, WordAt img (0x140 + 32 * j) w → WordAt img' (0x140 + 32 * j) w) →
      WordAt img' 0xa20 (Nat.toB256 v) → R ≤ g → g ≤ G →
      G = g + (10048 + costGetDMem x A.toNat) → M' = alD2Mem M x0 x1 x2 A x v →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_170b_c1339 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M G) X Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 5079 + costGetDMem x A.toNat + 19 + 120 + (67 * 71 + 56) + 6 +
      11 := ⟨G - costGetDMem x A.toNat - 10048, by omega⟩
  have hXe : X =
      alD2Pre (svItL 0x0a 0xa0 0x0a 0x40 0x16 0x66 (lpBr 71 alIdx5 0x16 0x44 t_1666_c939 0)) := by
    rcases hctx with rfl | rfl
    · exact al_d2_c69
    · exact al_d2_c93
  rw [hXe]
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xaa0) (c := 6) hR hW hsz rfl (by decide) ?_
  clear hR hW hsz; rename' M => Mq0; intro M hMq0 hR hW hsz; have hRq := hR
  rw [show memExtSize 0xaa0 0xaa0 32 = 0xac0 by decide] at hsz
  refine rx_svFromLM (fun o => Bytes.toB256 ((Bytes.writeAt img 0xaa0
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0xaa0) (Lm := 0xa40) (sz := 0xac0)
    rfl rfl (by decide) (by decide) (by decide) (by decide) al_sv5_chain 71 (n := 0) rfl hR hW hsz
    (by wauto) (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hMsv hR hW hsz hk1 hct1
  have hI : ∀ o w, o + 32 ≤ 0xaa0 → WordAt img o w →
      WordAt (Bytes.writeAt img 0xaa0 (Bytes.toB256 [1, 64]).toBytes) o w := fun o w ho h => by
    wauto
  have g0 := hk1 _ _ (hI _ _ (by decide) hx0) (.inl (by decide))
  have g1' := hk1 _ _ (hI _ _ (by decide) hx1) (.inl (by decide))
  have g2 := hk1 _ _ (hI _ _ (by decide) hx2) (.inl (by decide))
  have gA := hk1 _ _ (hI _ _ (by decide) hA) (.inl (by decide))
  -- the arguments of `get_D_mem`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x460) (v := x0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH g0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xac0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0xac0 0xac0 32 = 0xae0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := x1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g1') (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0xae0) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0xae0 0xae0 32 = 0xb00 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x4a0) (v := x2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0xb00) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0xb00 0xb00 32 = 0xb20 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1e0) (v := A) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH gA) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xb20) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0xb20 0xb20 32 = 0xb40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0xb20) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0xb00) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0xae0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0xac0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, ⟨-, hW2, hsz2⟩, hEq2⟩ := getDMem_exactL (G := g1 + 5079) (ρ := Nat.toB256 (0x16a1 + 6))
    (S := exSaved (fun o => Bytes.toB256 ((Bytes.writeAt img 0xaa0
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (0x140 + 32 * 0) (71 + 1) ++ S)
    (M := M) hX hres hW hsz (by decide) (by decide) (by simp only [List.length_append, exSaved_length]; omega)
  refine rxe_pcCall rli_prog_29 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  clear hR hW hsz hrun
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  have hs2x := hsz2
  clear hW2 hsz2
  -- `D2` parked, the restore counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xb80) (c := 13) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0xb40 0xb80 32 = 0xba0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xaa0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0xba0 0xaa0 32 = 0xba0 by decide] at hsz
  rw [al_rs5_first]
  refine rx_rsFromLM (fun o => Bytes.toB256 ((Bytes.writeAt img 0xaa0
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0xaa0) (sz := 0xba0)
    rfl (by decide) (by decide) (by decide) al_rs5_chain 71 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hMrs hR3 hW3 hsz3 hm3 hk3
  have hD3 : WordAt img3 0xb80 (Nat.toB256 v) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have rr : ∀ j, j ≤ 71 → ∀ w, WordAt img (0x140 + 32 * j) w → WordAt img3 (0x140 + 32 * j) w :=
    fun j hj w h => cw_restored (hm3 j hj) (hI _ _ (by omega) h)
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `D2` stored at `0xa20`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xb80) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xa20) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0xba0 0xa20 32 = 0xba0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_jump al_prog_1339 ·)
  exact k M _ g1 hR hW hsz (fun j hj w h => by have := rr j (by omega) w h; wauto) (by wauto)
    (by omega) (by omega) (by omega)
    (alD2Mem_eq hMq0 hRq hMsv hMq1 hMq2 hMq3 hMq4 hEq2 hs2x hMq5 hMq6 hMrs hMq7)

/-- **`D2`, forward** (see the module note). -/
theorem rx_al_d2 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R v : Nat} {Q : Outcome → Prop} {x : V3} {A x0 x1 x2 : B256} {X : SFunc}
    (hctx : X = t_163a_c69 ∨ X = t_163a_c93)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xaa0)
    (hA : WordAt img 0x1e0 A) (hx0 : WordAt img 0x460 x0) (hx1 : WordAt img 0x480 x1)
    (hx2 : WordAt img 0x4a0 x2)
    (hX : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some x)
    (hres : getDChk x.get A.toNat 1 = some v)
    (hG : R + costGetDMem x A.toNat + 15000 ≤ G) (hroom : S.length + 150 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xba0 →
      (∀ j, j < 71 → ∀ w, WordAt img (0x140 + 32 * j) w → WordAt img' (0x140 + 32 * j) w) →
      WordAt img' 0xa20 (Nat.toB256 v) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_170b_c1339 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M G) X Q :=
  rx_al_d2E hctx hR hW hsz hA hx0 hx1 hx2 hX hres hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7

end Blanc.Lift.Curve3Pool
