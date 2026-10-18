import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveLoop

/-!
# `_calc_withdraw_one_coin`, forward: the second `get_y_D`, `dy`, the fee and the return

`rx_cw_e` (the fee loop's exit `t_41db_c79` → the return): `xp_reduced[i]` kept on the stack,
the save of `[0x140, 0x780)`, `get_y_D(amp, i, xp_reduced, D1)` (`getYD_exact`) parked at
`0x8a0`, the restore, the checked `dy = (xp_reduced[i] - y - 1) / PRECISION_MUL[i]` and
`dy_0 - dy`, both returned to `ρ`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def cwIdx7 : List Nat := [101, 122, 144, 166, 188, 206, 220, 234, 248, 263, 278, 293, 308, 323,
  338, 353, 368, 383, 398, 413, 427, 441, 455, 469, 483, 499, 513, 527, 543, 556, 569, 580, 591,
  601, 611, 621, 631, 641, 651, 661, 671, 681, 690, 699, 708, 717, 726, 735, 744]

def cwIdx8 : List Nat := [754, 764, 773, 782, 791, 800, 809, 818, 827, 836, 845, 854, 863, 872,
  881, 890, 899, 908, 917, 926, 934, 942, 950, 958, 966, 974, 982, 990, 998, 1006, 1014, 1022,
  1030, 1038, 1046, 1054, 1062, 1070, 1077, 1084, 1091, 1098, 1105, 1112, 1119, 1126, 1133, 1140,
  1147]

theorem cw_sv4_first :
    t_41fe_c79 = svIt 0x07 0x80 0x42 0x20 (lpBr 49 cwIdx7 0x41 0xfe t_4220_c744 0) := rfl

theorem cw_sv4_chain : ∀ n, n < 49 → cert.prog[cwIdx7.getD n 0]? =
    some (svIt 0x07 0x80 0x42 0x20 (lpBr 49 cwIdx7 0x41 0xfe t_4220_c744 (n + 1))) := by
  decide +kernel

theorem cw_rs4_first :
    t_4285_c744 = rsIt 0x07 0x80 0x42 0xa8 (lpBr 49 cwIdx8 0x42 0x85 t_42a8_c1147 0) := rfl

theorem cw_rs4_chain : ∀ n, n < 49 → cert.prog[cwIdx8.getD n 0]? =
    some (rsIt 0x07 0x80 0x42 0xa8 (lpBr 49 cwIdx8 0x42 0x85 t_42a8_c1147 (n + 1))) := by
  decide +kernel

theorem cw_prog_1154 : cert.prog[1154]? = some t_4353_c1154 := by decide +kernel
theorem cw_prog_1161 : cert.prog[1161]? = some t_4353_c1161 := by decide +kernel
theorem cw_prog_1168 : cert.prog[1168]? = some t_4381_c1168 := by decide +kernel

/-- **The second `get_y_D`, `dy` and the return, forward.** -/
theorem rx_cw_e {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {iw r0 r1 r2 Aw D1 y2 dy0 ρ : B256}
    (hi3 : iw.toNat < 3)
    (hy2 : getYDChk Aw.toNat ⟨iw.toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get D1.toNat =
      some y2.toNat)
    (hs0 : ¬ pickWord3 iw.toNat r0 r1 r2 < y2)
    (hs1 : ¬ pickWord3 iw.toNat r0 r1 r2 - y2 < Bytes.toB256 [1])
    (hs2 : ¬ dy0 < cwDy iw r0 r1 r2 y2)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x760)
    (hA : WordAt img 0x1a0 Aw) (hi : WordAt img 0x160 iw) (hr0 : WordAt img 0x540 r0)
    (hr1 : WordAt img 0x560 r1) (hr2 : WordAt img 0x580 r2) (hD1 : WordAt img 0x520 D1)
    (hd : WordAt img 0x700 dy0) (hrho : WordAt img 0x180 ρ) (hp0 : WordAt img 0x220 cwP1)
    (hp1 : WordAt img 0x240 cwPm) (hp2 : WordAt img 0x260 cwPm)
    (hG : costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat D1.toNat + 7684 + R ≤ G)
    (hroom : S.length + 70 < 1024)
    (hQ : ∀ (M' : Mem) (g : Nat), Mem.Wf M' → M'.size = 0x920 → R ≤ g → g ≤ G →
      Q (.returned (St b (cwDy iw r0 r1 r2 y2 :: (dy0 - cwDy iw r0 r1 r2 y2) :: S) M' g))) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_41db_c79 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 4097 + costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      D1.toNat + 19 + 162 + (67 * 49 + 56) + 67 :=
    ⟨G - costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat D1.toNat - 7684, by omega⟩
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hi) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hi3) ·)
  -- tree t_41f1_c79
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (v := pickWord3 iw.toNat r0 r1 r2) (o := 0x540 + 32 * iw.toNat) hR hsz (ex_off (bw := Bytes.toB256 [5, 0x40]) hi3 (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoH (wordAt_pick hi3 hr0 hr1 hr2)) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x780) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x760 0x780 32 = 0x7a0 by decide] at hsz
  rw [cw_sv4_first]
  refine rx_svFrom (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x780) (sz := 0x7a0)
    (by decide) rfl (by decide) (by decide) cw_sv4_chain 49 (n := 0) rfl hR hW hsz (by wauto)
    (fun m _ _ => by wautoH (wordAt_self img _)) (by simp only [List.length_cons]; omega) ?_
  clear hR hW hsz
  intro M1 img1 hR hW hsz hk1 hc1
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1a0) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ (by wautoH hA) (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x7a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x7a0 0x7a0 32 = 0x7c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ (by wautoH hi) (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x7c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x7c0 0x7c0 32 = 0x7e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x540) (v := r0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ (by wautoH hr0) (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x7e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x7e0 0x7e0 32 = 0x800 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x560) (v := r1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ (by wautoH hr1) (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x800) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x800 0x800 32 = 0x820 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x580) (v := r2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ (by wautoH hr2) (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x820) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x820 0x820 32 = 0x840 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x520) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ (by wautoH hD1) (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x840) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x840 0x840 32 = 0x860 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x840) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x820) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x800) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x7e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x7c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x7a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hso, hrun⟩ := getYD_exact (G := g1 + 4097) (ρ := Nat.toB256 (0x4273 + 6))
    (S := exSaved (fun o => Bytes.toB256 (img.sliceD o 32 0)) (0x140 + 32 * 0) (49 + 1) ++
      pickWord3 iw.toNat r0 r1 r2 :: S)
    (M := M) (by omega) (by omega)
    (by simp only [List.length_append, exSaved_length, List.length_cons]; omega) hi3 hy2
  refine rxe_pcCall cw_prog_753 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  have hW2 := hso.wf hW
  have hsz2 : M2.size = 0x860 := by rw [hso.size, hsz]
  clear hR hW hsz hrun hso
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  clear hW2 hsz2
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x8a0) (c := 13) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x860 0x8a0 32 = 0x8c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x780) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x8c0 0x780 32 = 0x8c0 by decide] at hsz
  rw [cw_rs4_first]
  refine rx_rsFrom (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x780) (sz := 0x8c0)
    (by decide) rfl (by decide) (by decide) cw_rs4_chain 49 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hR3 hW3 hsz3 hm3 hk3
  have hy3 : WordAt img3 0x8a0 (Nat.toB256 y2.toNat) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  rw [toB256_toNat] at hy3
  have rhi := cw_restored (hm3 1 (by omega)) hi
  have rhrho := cw_restored (hm3 2 (by omega)) hrho
  have rhd := cw_restored (hm3 46 (by omega)) hd
  have rhp0 := cw_restored (hm3 7 (by omega)) hp0
  have rhp1 := cw_restored (hm3 8 (by omega)) hp1
  have rhp2 := cw_restored (hm3 9 (by omega)) hp2
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x8a0) (v := y2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hy3) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs0) ·)
  -- tree t_42b9_c1147
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x760) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x8c0 0x760 32 = 0x8c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x760) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs1) ·)
  -- tree t_42d7_c1147
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
  -- tree t_42f2_c1147
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (v := pickWord3 iw.toNat cwP1 cwPm cwPm) (o := 0x220 + 32 * iw.toNat) hR hsz (ex_off (bw := Bytes.toB256 [2, 0x20]) hi3 (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoH (wordAt_pick hi3 rhp0 rhp1 rhp2)) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (cw_pm_ne hi3) ·)
  -- tree t_4302_c1147
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x760) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x8c0 0x760 32 = 0x8c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x760) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x8c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x8c0 0x8c0 32 = 0x8e0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x700) (v := dy0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rhd) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x760) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs2) ·)
  -- tree t_4337_c1147
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x8e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x8e0 0x8e0 32 = 0x900 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x900 0xc0 32 = 0x900 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0xc0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x900) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x900 0x900 32 = 0x920 by decide] at hsz
  -- tree t_4353_c1147
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_4365_c1147
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_sub (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x8e0) hR hsz (cw_off (by decide) (by decide)) (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_sub (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x900 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_jump cw_prog_1154 ·)
  -- tree t_4353_c1154
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_4365_c1154
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_sub (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x8c0) hR hsz (cw_off (by decide) (by decide)) (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_sub (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x900 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_jump cw_prog_1161 ·)
  -- tree t_4353_c1161
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_zero' (by decide) ·)
  -- tree t_4361_c1161
  xr (rx_push rfl (by hrs) ·)
  xr (rx_jump cw_prog_1168 ·)
  -- tree t_4381_c1168
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x180) (v := ρ) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rhrho) (by hrs) ·)
  -- ATOM .ret
  exact ⟨_, rx_ret, hQ M g1 hW hsz (by omega) (by omega)⟩

end Blanc.Lift.Curve3Pool
