import Blanc.Lift.Curve3Pool.Walk.RliLiveD

/-!
# `remove_liquidity_imbalance`, forward: `D1`

`rx_rli_d1` (`t_32c1_c572` → the fee loop's head `t_336e_c1039`): the save of
`[0x140, 0x4a0)`, `D1 = get_D_mem(new_balances, amp)` (`getDMem_exact`), the restore, `D1`
at `0x480`, `fees` cleared and the loop counter at `0x600` set.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def rliIdx3 : List Nat := [583, 594, 604, 614, 624, 634, 644, 654, 664, 674, 683, 692, 701, 710,
  719, 728, 737, 746, 756, 766, 775, 784, 793, 802, 811, 820]

def rliIdx4 : List Nat := [829, 838, 847, 856, 865, 874, 883, 892, 901, 910, 919, 927, 935, 943,
  951, 959, 967, 975, 983, 991, 999, 1007, 1015, 1023, 1031, 1039]

theorem rli_sv2_first :
    t_32c1_c572 = svIt 0x04 0xa0 0x32 0xe3 (lpBr 26 rliIdx3 0x32 0xc1 t_32e3_c820 0) := rfl

theorem rli_sv2_chain : ∀ n, n < 26 → cert.prog[rliIdx3.getD n 0]? =
    some (svIt 0x04 0xa0 0x32 0xe3 (lpBr 26 rliIdx3 0x32 0xc1 t_32e3_c820 (n + 1))) := by
  decide +kernel

theorem rli_rs2_first :
    t_3330_c820 = rsIt 0x04 0xa0 0x33 0x53 (lpBr 26 rliIdx4 0x33 0x30 t_3353_c1039 0) := rfl

theorem rli_rs2_chain : ∀ n, n < 26 → cert.prog[rliIdx4.getD n 0]? =
    some (rsIt 0x04 0xa0 0x33 0x53 (lpBr 26 rliIdx4 0x33 0x30 t_3353_c1039 (n + 1))) := by
  decide +kernel

/-- **`D1`, forward.** -/
theorem rx_rli_d1 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R v : Nat} {Q : Outcome → Prop} {x : V3}
    {T F AF Aw b0 b1 b2 n0 n1 n2 D0 : B256}
    (hX : xpChk ⟨n0.toNat, n1.toNat, n2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x520)
    (hctr : WordAt img 0x4a0 (Nat.toB256 0x140)) (hT : WordAt img 0x140 T)
    (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw)
    (hb0 : WordAt img 0x280 b0) (hb1 : WordAt img 0x2a0 b1) (hb2 : WordAt img 0x2c0 b2)
    (hn0 : WordAt img 0x2e0 n0) (hn1 : WordAt img 0x300 n1) (hn2 : WordAt img 0x320 n2)
    (hD0 : WordAt img 0x340 D0)
    (hG : costGetDMem x Aw.toNat + 7000 + R ≤ G) (hroom : S.length + 100 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x620 → WordAt img' 0x140 T → WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x280 b0 → WordAt img' 0x2a0 b1 →
      WordAt img' 0x2c0 b2 → WordAt img' 0x2e0 n0 → WordAt img' 0x300 n1 → WordAt img' 0x320 n2 →
      WordAt img' 0x340 D0 → WordAt img' 0x480 (Nat.toB256 v) →
      WordAt img' 0x600 (Bytes.toB256 [0]) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1039 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_32c1_c572 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 1971 + costGetDMem x Aw.toNat + 19 + 110 + (67 * 26 + 56) :=
    ⟨G - costGetDMem x Aw.toNat - 3898, by omega⟩
  rw [rli_sv2_first]
  refine rx_svFrom (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x4a0) (sz := 0x520)
    (by decide) rfl (by decide) (by decide) rli_sv2_chain 26 (n := 0) rfl hR hW hsz hctr
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hR hW hsz hk1 hct1
  -- the arguments of `get_D_mem`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := n0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hn0 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x4c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x4c0 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x300) (v := n1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hn1 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x4e0) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x4e0 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := n2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hn2 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x500) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x500 32 = 0x520 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x220) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hAw (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x520) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x520 32 = 0x540 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x520) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x500) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x4e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x4c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, -, hW2, hsz2⟩ := getDMem_exact (G := g1 + 1971) (ρ := Nat.toB256 (0x331e + 6))
    (S := exSaved (fun o => Bytes.toB256 (img.sliceD o 32 0)) (0x140 + 32 * 0) (26 + 1) ++ S)
    (M := M) hX hres hW hsz (by decide) (by decide)
    (by simp only [List.length_append, exSaved_length]; omega)
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
  refine rxe_mstore (o := 0x580) (c := 12) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x540 0x580 32 = 0x5a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x4a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x5a0 0x4a0 32 = 0x5a0 by decide] at hsz
  rw [rli_rs2_first]
  refine rx_rsFrom (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x4a0) (sz := 0x5a0)
    (by decide) rfl (by decide) (by decide) rli_rs2_chain 26 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hR3 hW3 hsz3 hm3 hk3
  have hD3 : WordAt img3 0x580 (Nat.toB256 v) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have rT := cw_restored (hm3 0 (by omega)) hT
  have rF := cw_restored (hm3 5 (by omega)) hF
  have rAF := cw_restored (hm3 6 (by omega)) hAF
  have rAw := cw_restored (hm3 7 (by omega)) hAw
  have rb0 := cw_restored (hm3 10 (by omega)) hb0
  have rb1 := cw_restored (hm3 11 (by omega)) hb1
  have rb2 := cw_restored (hm3 12 (by omega)) hb2
  have rn0 := cw_restored (hm3 13 (by omega)) hn0
  have rn1 := cw_restored (hm3 14 (by omega)) hn1
  have rn2 := cw_restored (hm3 15 (by omega)) hn2
  have rD0 := cw_restored (hm3 16 (by omega)) hD0
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `D1`, `fees`, the loop counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x580) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x480) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x5a0 0x480 32 = 0x5a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldatasize (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_calldatacopy (o := 0x5a0) (z := 0x60) (c := 22) hR hW hsz (by decide) (by decide) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x5a0 0x5a0 0x60 = 0x600 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x600) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x600 0x600 32 = 0x620 by decide] at hsz
  xr (rx_add (by hrs) ·)
  exact k M _ g1 hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega)
    (by omega)

end Blanc.Lift.Curve3Pool
