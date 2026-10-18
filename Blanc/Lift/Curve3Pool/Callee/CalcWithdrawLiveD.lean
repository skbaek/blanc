import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveC

/-!
# `_calc_withdraw_one_coin`, forward: the first `get_y_D` and `dy_0`

`rx_cw_d` (`t_3f41_c984` → the fee loop `t_405e_c1348`): the save of `[0x140, 0x5c0)`,
`new_y = get_y_D(amp, i, xp, D1)` (`getYD_exact`) parked at `0x6e0`, the restore, `new_y` at
`0x5a0`, and the checked `dy_0 = (xp[i] - new_y) / PRECISION_MUL[i]` at `0x700`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def cwIdx5 : List Nat := [992, 1000, 1008, 1016, 1024, 1032, 1040, 1049, 1057, 1065, 1072, 1079,
  1086, 1093, 1100, 1107, 1114, 1121, 1128, 1135, 1142, 1149, 1156, 1163, 1170, 1176, 1181, 1186,
  1191, 1196, 1201, 1206, 1211, 1216, 1221]

def cwIdx6 : List Nat := [1226, 1231, 1236, 1241, 1246, 1251, 1256, 1261, 1266, 1271, 1276, 1280,
  1284, 1287, 1290, 1293, 1296, 1299, 1302, 1305, 1308, 1311, 1314, 1317, 1320, 1323, 1326, 1329,
  1332, 1335, 1338, 1341, 1344, 1346, 1348]

theorem cw_sv3_first :
    t_3f41_c984 = svIt 0x05 0xc0 0x3f 0x63 (lpBr 35 cwIdx5 0x3f 0x41 t_3f63_c1221 0) := rfl

theorem cw_sv3_chain : ∀ n, n < 35 → cert.prog[cwIdx5.getD n 0]? =
    some (svIt 0x05 0xc0 0x3f 0x63 (lpBr 35 cwIdx5 0x3f 0x41 t_3f63_c1221 (n + 1))) := by
  decide +kernel

theorem cw_rs3_first :
    t_3fc8_c1221 = rsIt 0x05 0xc0 0x3f 0xeb (lpBr 35 cwIdx6 0x3f 0xc8 t_3feb_c1348 0) := rfl

theorem cw_rs3_chain : ∀ n, n < 35 → cert.prog[cwIdx6.getD n 0]? =
    some (rsIt 0x05 0xc0 0x3f 0xeb (lpBr 35 cwIdx6 0x3f 0xc8 t_3feb_c1348 (n + 1))) := by
  decide +kernel

theorem cw_prog_753 : cert.prog[753]? = some t_3999_c753 := cw_yd_prog

/-- An indexed word of a three-word array. -/
theorem wordAt_pick {img : Bytes} {base i : Nat} {x0 x1 x2 : B256} (hi : i < 3)
    (h0 : WordAt img base x0) (h1 : WordAt img (base + 32) x1) (h2 : WordAt img (base + 64) x2) :
    WordAt img (base + 32 * i) (pickWord3 i x0 x1 x2) := by
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  · exact h0
  · exact h1
  · exact h2

theorem cw_pm_ne {iw : B256} (hi : iw.toNat < 3) : pickWord3 iw.toNat cwP1 cwPm cwPm ≠ 0 := by
  obtain h | h | h : iw.toNat = 0 ∨ iw.toNat = 1 ∨ iw.toNat = 2 := by omega
  all_goals rw [h]; decide

/-- **The first `get_y_D` and `dy_0`, forward.** -/
theorem rx_cw_d {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {x0 x1 x2 Aw iw D1 y : B256}
    (hi3 : iw.toNat < 3)
    (hy : getYDChk Aw.toNat ⟨iw.toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D1.toNat =
      some y.toNat)
    (hyl : ¬ pickWord3 iw.toNat x0 x1 x2 < y)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0)
    (hctr : WordAt img 0x5c0 (Nat.toB256 0x140)) (hA : WordAt img 0x1a0 Aw)
    (hi : WordAt img 0x160 iw) (hx0 : WordAt img 0x320 x0) (hx1 : WordAt img 0x340 x1)
    (hx2 : WordAt img 0x360 x2) (hD1 : WordAt img 0x520 D1) (hp0 : WordAt img 0x220 cwP1)
    (hp1 : WordAt img 0x240 cwPm) (hp2 : WordAt img 0x260 cwPm)
    (hG : costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat D1.toNat + 5344 + R ≤ G)
    (hroom : S.length + 50 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x740 →
      (∀ m v, m < 35 → WordAt img (0x140 + 32 * m) v → WordAt img' (0x140 + 32 * m) v) →
      WordAt img' 0x5a0 y → WordAt img' 0x700
        ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm) →
      WordAt img' 0x720 (Bytes.toB256 [0]) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_405e_c1348 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_3f41_c984 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 2762 + costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat
      D1.toNat + 19 + 162 + (67 * 35 + 56) :=
    ⟨G - costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat D1.toNat - 5344, by omega⟩
  rw [cw_sv3_first]
  refine rx_svFrom (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x5c0) (sz := 0x5e0)
    (by decide) rfl (by decide) (by decide) cw_sv3_chain 35 (n := 0) rfl hR hW hsz hctr
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hR hW hsz hk1 hc1
  -- the arguments of `get_y_D`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1a0) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hA (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x5e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x5e0 0x5e0 32 = 0x600 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hi (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x600) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x600 0x600 32 = 0x620 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := x0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hx0 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x620) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x620 0x620 32 = 0x640 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := x1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hx1 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x640) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x640 0x640 32 = 0x660 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x360) (v := x2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hx2 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x660) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x660 0x660 32 = 0x680 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x520) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hD1 (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x680) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x680 0x680 32 = 0x6a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x680) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x660) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x640) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x600) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x5e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hso, hrun⟩ := getYD_exact (G := g1 + 2762) (ρ := Nat.toB256 (0x3fb6 + 6))
    (S := exSaved (fun o => Bytes.toB256 (img.sliceD o 32 0)) (0x140 + 32 * 0) (35 + 1) ++ S)
    (M := M) (by omega) (by omega)
    (by simp only [List.length_append, exSaved_length]; omega) hi3 hy
  refine rxe_pcCall cw_prog_753 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  have hW2 := hso.wf hW
  have hsz2 : M2.size = 0x6a0 := by rw [hso.size, hsz]
  clear hR hW hsz hrun hso
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  clear hW2 hsz2
  -- `new_y` parked, the restore counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x6e0) (c := 13) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x6a0 0x6e0 32 = 0x700 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x5c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x700 0x5c0 32 = 0x700 by decide] at hsz
  rw [cw_rs3_first]
  refine rx_rsFrom (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x5c0) (sz := 0x700)
    (by decide) rfl (by decide) (by decide) cw_rs3_chain 35 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hR3 hW3 hsz3 hm3 hk3
  have hy3 : WordAt img3 0x6e0 (Nat.toB256 y.toNat) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  rw [toB256_toNat] at hy3
  have rhi := cw_restored (hm3 1 (by omega)) hi
  have rhx0 := cw_restored (hm3 15 (by omega)) hx0
  have rhx1 := cw_restored (hm3 16 (by omega)) hx1
  have rhx2 := cw_restored (hm3 17 (by omega)) hx2
  have rhp0 := cw_restored (hm3 7 (by omega)) hp0
  have rhp1 := cw_restored (hm3 8 (by omega)) hp1
  have rhp2 := cw_restored (hm3 9 (by omega)) hp2
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `dy_0`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x6e0) (v := y) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hy3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x5a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x700 0x5a0 32 = 0x700 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rhi) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hi3) ·)
  -- tree t_4007_c1348
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (v := pickWord3 iw.toNat x0 x1 x2) (o := 0x320 + 32 * iw.toNat) hR hsz (ex_off (bw := Bytes.toB256 [3, 0x20]) hi3 (by decide) (by decide)) ⟨by omega, by decide⟩ ((wordAt_pick hi3 rhx0 rhx1 rhx2).write_other (by simp only [B256.length_toBytes]; omega)) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x5a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hyl) ·)
  -- tree t_401d_c1348
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rhi) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hi3) ·)
  -- tree t_4038_c1348
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (v := pickWord3 iw.toNat cwP1 cwPm cwPm) (o := 0x220 + 32 * iw.toNat) hR hsz (ex_off (bw := Bytes.toB256 [2, 0x20]) hi3 (by decide) (by decide)) ⟨by omega, by decide⟩ ((wordAt_pick hi3 rhp0 rhp1 rhp2).write_other (by simp only [B256.length_toBytes]; omega)) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (cw_pm_ne hi3) ·)
  -- tree t_4048_c1348
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x700) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x700 0x700 32 = 0x720 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x720) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x720 0x720 32 = 0x740 by decide] at hsz
  xr (rx_add (by hrs) ·)
  exact k M _ g1 hR hW hsz (fun m v hm' hv => by wautoH (cw_restored (hm3 m (by omega)) hv))
    (by wauto) (by wauto) (by wauto) (by omega) (by omega)

end Blanc.Lift.Curve3Pool
