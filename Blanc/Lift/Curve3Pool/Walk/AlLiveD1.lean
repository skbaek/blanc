import Blanc.Lift.Curve3Pool.Walk.AlLiveLoop

/-!
# `add_liquidity`, forward: `D1`

`rx_al_d1` (the loop's exit `t_1333_c41` (memory `0x840`) or `t_1333_c6` (`0x900`) →
`t_13e9_c1273`): the save of `[0x140, 0x920)`, `D1 = get_D_mem(new_balances, amp)`
(`getDMem_exact` over a memory of `0x9c0`), the restore, `D1` at `0x900`, and `assert D1 > D0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alIdx3 : List Nat := [42, 67, 92, 113, 134, 156, 178, 198, 216, 230, 244, 259, 274, 289, 304, 319, 334, 349, 364,
  379, 394, 409, 423, 437, 451, 465, 479, 495, 509, 523, 539, 552, 565, 576, 587, 597, 607, 617,
  627, 637, 647, 657, 667, 677, 686, 695, 704, 713, 722, 731, 740, 749, 759, 769, 778, 787, 796,
  805, 814, 823, 832, 841]

def alIdx4 : List Nat := [850, 859, 868, 877, 886, 895, 904, 913, 922, 930, 938, 946, 954, 962, 970, 978, 986, 994, 1002,
  1010, 1018, 1026, 1034, 1042, 1051, 1059, 1067, 1074, 1081, 1088, 1095, 1102, 1109, 1116, 1123,
  1130, 1137, 1144, 1151, 1158, 1165, 1172, 1178, 1183, 1188, 1193, 1198, 1203, 1208, 1213, 1218,
  1223, 1228, 1233, 1238, 1243, 1248, 1253, 1258, 1263, 1268, 1273]

theorem al_sv3_c41 :
    t_133d_c41 = svIt 0x09 0x20 0x13 0x5f (lpBr 62 alIdx3 0x13 0x3d t_135f_c841 0) := rfl

theorem al_sv3_c6 :
    t_133d_c6 = svIt 0x09 0x20 0x13 0x5f (lpBr 62 alIdx3 0x13 0x3d t_135f_c841 0) := rfl

theorem al_sv3_chain : ∀ n, n < 62 → cert.prog[alIdx3.getD n 0]? =
    some (svIt 0x09 0x20 0x13 0x5f (lpBr 62 alIdx3 0x13 0x3d t_135f_c841 (n + 1))) := by
  decide +kernel

theorem al_rs3_first :
    t_13ac_c841 = rsIt 0x09 0x20 0x13 0xcf (lpBr 62 alIdx4 0x13 0xac t_13cf_c1273 0) := rfl

theorem al_rs3_chain : ∀ n, n < 62 → cert.prog[alIdx4.getD n 0]? =
    some (rsIt 0x09 0x20 0x13 0xcf (lpBr 62 alIdx4 0x13 0xac t_13cf_c1273 (n + 1))) := by
  decide +kernel

/-- The loop's exit before the save: drop the loop words, set the save counter. -/
def alD1Pre (f : SFunc) : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x01, 0x40] (by decide))
    (.next (.push [0x09, 0x20] (by decide)) (.next (.reg .mstore) f)))))

theorem al_d1_c41 : t_1333_c41 =
    alD1Pre (svIt 0x09 0x20 0x13 0x5f (lpBr 62 alIdx3 0x13 0x3d t_135f_c841 0)) := rfl

theorem al_d1_c6 : t_1333_c6 =
    alD1Pre (svIt 0x09 0x20 0x13 0x5f (lpBr 62 alIdx3 0x13 0x3d t_135f_c841 0)) := rfl

/-- **`D1`, forward** (see the module note). -/
theorem rx_al_d1 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R v s c0 : Nat} {Q : Outcome → Prop} {x : V3} {F AF A T D0 : B256} {old nv : Nat → B256}
    {X : SFunc}
    (hctx : (s = 0x840 ∧ c0 = 29 ∧ X = t_1333_c41) ∨ (s = 0x900 ∧ c0 = 9 ∧ X = t_1333_c6))
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hm : AlPullImg img 3 F AF A T D0 old nv)
    (hX : xpChk ⟨(nv 0).toNat, (nv 1).toNat, (nv 2).toNat⟩ = some x)
    (hres : getDChk x.get A.toNat 1 = some v) (hlt : D0 < Nat.toB256 v)
    (hG : R + costGetDMem x A.toNat + 12000 ≤ G) (hroom : S.length + 140 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xa20 → AlPullImg img' 3 F AF A T D0 old nv →
      WordAt img' 0x900 (Nat.toB256 v) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_13e9_c1273 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) X Q := by
  have hc0 : c0 ≤ 29 := by omega
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 4466 + costGetDMem x A.toNat + 19 + 120 + (67 * 62 + 56) + c0 +
      11 := ⟨G - costGetDMem x A.toNat - 8826 - c0, by omega⟩
  have hXe : X = alD1Pre (svIt 0x09 0x20 0x13 0x5f (lpBr 62 alIdx3 0x13 0x3d t_135f_c841 0)) := by
    rcases hctx with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact al_d1_c41
    · exact al_d1_c6
  rw [hXe]
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x920) (c := c0) hR hW hsz rfl
    (by rcases hctx with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> decide) ?_
  have hs' : memExtSize s 0x920 32 = 0x940 := by rcases hctx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  clear hR hW hsz M; intro M hR hW hsz; rw [hs'] at hsz
  refine rx_svFrom (fun o => Bytes.toB256 ((Bytes.writeAt img 0x920
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0x920) (sz := 0x940)
    (by decide) rfl (by decide) (by decide) al_sv3_chain 62 (n := 0) rfl hR hW hsz (by wauto)
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hR hW hsz hk1 hct1
  have hI : ∀ o w, o + 32 ≤ 0x920 → WordAt img o w →
      WordAt (Bytes.writeAt img 0x920 (Bytes.toB256 [1, 64]).toBytes) o w := fun o w ho h => by
    wauto
  have g0 := hk1 _ _ (hI _ _ (by decide) hm.n0) (.inl (by decide))
  have g1' := hk1 _ _ (hI _ _ (by decide) hm.n1) (.inl (by decide))
  have g2 := hk1 _ _ (hI _ _ (by decide) hm.n2) (.inl (by decide))
  have gA := hk1 _ _ (hI _ _ (by decide) hm.m0.amp) (.inl (by decide))
  -- the arguments of `get_D_mem`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x460) (v := nv 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH g0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x940) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x940 0x940 32 = 0x960 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := nv 1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g1') (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x960) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x960 0x960 32 = 0x980 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x4a0) (v := nv 2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x980) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x980 0x980 32 = 0x9a0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1e0) (v := A) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH gA) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x9a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x9a0 0x9a0 32 = 0x9c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x9a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x980) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x960) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x940) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, -, hW2, hsz2⟩ := getDMem_exact (G := g1 + 4466) (ρ := Nat.toB256 (0x139a + 6))
    (S := exSaved (fun o => Bytes.toB256 ((Bytes.writeAt img 0x920
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (0x140 + 32 * 0) (62 + 1) ++ S)
    (M := M) hX hres hW hsz (by decide) (by decide) (by simp only [List.length_append, exSaved_length]; omega)
  refine rxe_pcCall rli_prog_29 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  clear hR hW hsz hrun
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  clear hW2 hsz2
  -- `D1` parked, the restore counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xa00) (c := 13) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x9c0 0xa00 32 = 0xa20 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x920) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xa20 0x920 32 = 0xa20 by decide] at hsz
  rw [al_rs3_first]
  refine rx_rsFrom (fun o => Bytes.toB256 ((Bytes.writeAt img 0x920
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0x920) (sz := 0xa20)
    (by decide) rfl (by decide) (by decide) al_rs3_chain 62 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hR3 hW3 hsz3 hm3 hk3
  have hD3 : WordAt img3 0xa00 (Nat.toB256 v) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have rr : ∀ j, j ≤ 62 → ∀ w, WordAt img (0x140 + 32 * j) w → WordAt img3 (0x140 + 32 * j) w :=
    fun j hj w h => cw_restored (hm3 j hj) (hI _ _ (by omega) h)
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `D1` stored, `D1 > D0`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa00) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xa20 0x900 32 = 0xa20 by decide] at hsz
  have hP : AlPullImg img3 3 F AF A T D0 old nv :=
    ⟨⟨rr 0 (by omega) _ hm.m0.f0, rr 1 (by omega) _ hm.m0.f1, rr 2 (by omega) _ hm.m0.f2,
      rr 3 (by omega) _ hm.m0.fee, rr 4 (by omega) _ hm.m0.adm, rr 5 (by omega) _ hm.m0.amp,
      rr 8 (by omega) _ hm.m0.supply, rr 13 (by omega) _ hm.m0.d0, rr 14 (by omega) _ hm.m0.o0,
      rr 15 (by omega) _ hm.m0.o1, rr 16 (by omega) _ hm.m0.o2⟩, rr 28 (by omega) _ hm.ctr,
      rr 25 (by omega) _ hm.n0, rr 26 (by omega) _ hm.n1, rr 27 (by omega) _ hm.n2⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hP.m0.d0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wauto) (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (gtCheck_ne_zero_of_lt hlt) ·)
  exact k M _ g1 hR hW hsz (al_pullImg_keep hP fun o w hw h1 h2 => by wauto) (by wauto)
    (by omega) (by omega)

end Blanc.Lift.Curve3Pool
