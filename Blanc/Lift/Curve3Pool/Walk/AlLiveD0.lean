import Blanc.Lift.Curve3Pool.Walk.AlLiveFront
import Blanc.Lift.Curve3Pool.Walk.RliLiveD

/-!
# `add_liquidity`, forward: `D0` on a positive supply

`rx_al_d0` (`t_0f8f_c0` → the pull loop `t_1031_c4`): the save of `[0x140, 0x360)`,
`D0 = get_D_mem(old_balances, amp)` (`getDMem_exact_400`: the memory grows from `0x400` to
`0x520`), the restore, and `D0` stored at `0x2e0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alIdx1 : List Nat := [30, 55, 82, 104, 125, 147, 169, 191, 209, 223, 237, 251, 266, 281, 296,
  311]

def alIdx2 : List Nat := [326, 341, 356, 371, 386, 401, 416, 430, 444, 458, 472, 486, 502, 516,
  530, 546]

theorem al_sv1_first :
    t_0f96_c0 = svIt 0x03 0x60 0x0f 0xb8 (lpBr 16 alIdx1 0x0f 0x96 t_0fb8_c311 0) := rfl

theorem al_sv1_chain : ∀ n, n < 16 → cert.prog[alIdx1.getD n 0]? =
    some (svIt 0x03 0x60 0x0f 0xb8 (lpBr 16 alIdx1 0x0f 0x96 t_0fb8_c311 (n + 1))) := by
  decide +kernel

theorem al_rs1_first :
    t_1005_c311 = rsIt 0x03 0x60 0x10 0x28 (lpBr 16 alIdx2 0x10 0x05 t_1028_c546 0) := rfl

theorem al_rs1_chain : ∀ n, n < 16 → cert.prog[alIdx2.getD n 0]? =
    some (rsIt 0x03 0x60 0x10 0x28 (lpBr 16 alIdx2 0x10 0x05 t_1028_c546 (n + 1))) := by
  decide +kernel

/-- **`D0`, forward.** -/
theorem rx_al_d0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R v : Nat} {Q : Outcome → Prop} {x : V3} {F AF Aw T b0 b1 b2 : B256}
    (hX : xpChk ⟨b0.toNat, b1.toNat, b2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x360)
    (hf0 : WordAt img 0x140 0) (hf1 : WordAt img 0x160 0) (hf2 : WordAt img 0x180 0)
    (hF : WordAt img 0x1a0 F) (hAF : WordAt img 0x1c0 AF) (hAw : WordAt img 0x1e0 Aw)
    (hT : WordAt img 0x240 T) (hb0 : WordAt img 0x300 b0) (hb1 : WordAt img 0x320 b1)
    (hb2 : WordAt img 0x340 b2)
    (hG : costGetDMem x Aw.toNat + 3000 + R ≤ G) (hroom : S.length + 90 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x520 → WordAt img' 0x140 0 → WordAt img' 0x160 0 → WordAt img' 0x180 0 →
      WordAt img' 0x1a0 F → WordAt img' 0x1c0 AF → WordAt img' 0x1e0 Aw →
      WordAt img' 0x240 T → WordAt img' 0x2e0 (Nat.toB256 v) → WordAt img' 0x300 b0 →
      WordAt img' 0x320 b1 → WordAt img' 0x340 b2 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_1031_c4 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_0f8f_c0 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 1208 + costGetDMem x Aw.toNat + 28 + 19 + 120 +
      (67 * 16 + 56) + 12 := ⟨G - costGetDMem x Aw.toNat - 2515, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x360) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x360 0x360 32 = 0x380 by decide] at hsz
  rw [al_sv1_first]
  refine rx_svFrom (fun o => Bytes.toB256 ((Bytes.writeAt img 0x360
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0x360) (sz := 0x380)
    (by decide) rfl (by decide) (by decide) al_sv1_chain 16 (n := 0) rfl hR hW hsz (by wauto)
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hR hW hsz hk1 hct1
  have g0 := hk1 _ _ (show WordAt (Bytes.writeAt img 0x360 (Bytes.toB256 [1, 64]).toBytes) 0x300 b0
    by wauto) (.inl (by decide))
  have g1' := hk1 _ _ (show WordAt (Bytes.writeAt img 0x360 (Bytes.toB256 [1, 64]).toBytes) 0x320 b1
    by wauto) (.inl (by decide))
  have g2 := hk1 _ _ (show WordAt (Bytes.writeAt img 0x360 (Bytes.toB256 [1, 64]).toBytes) 0x340 b2
    by wauto) (.inl (by decide))
  have gA := hk1 _ _ (show WordAt (Bytes.writeAt img 0x360 (Bytes.toB256 [1, 64]).toBytes) 0x1e0 Aw
    by wauto) (.inl (by decide))
  -- the arguments of `get_D_mem`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x300) (v := b0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH g0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x380) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x380 0x380 32 = 0x3a0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := b1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g1') (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x3a0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x3a0 0x3a0 32 = 0x3c0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := b2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x3c0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x3c0 0x3c0 32 = 0x3e0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1e0) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH gA) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x3e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x3e0 0x3e0 32 = 0x400 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, -, hW2, hsz2⟩ := getDMem_exact_400 (G := g1 + 1208) (ρ := Nat.toB256 (0xff3 + 6))
    (S := exSaved (fun o => Bytes.toB256 ((Bytes.writeAt img 0x360
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (0x140 + 32 * 0) (16 + 1) ++ S)
    (M := M) hX hres hW hsz (by simp only [List.length_append, exSaved_length]; omega)
  refine rxe_pcCall rli_prog_29 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  clear hR hW hsz hrun
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  clear hW2 hsz2
  -- `D0` parked, the restore counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x440) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x440 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x360) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x360 32 = 0x520 by decide] at hsz
  rw [al_rs1_first]
  refine rx_rsFrom (fun o => Bytes.toB256 ((Bytes.writeAt img 0x360
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0x360) (sz := 0x520)
    (by decide) rfl (by decide) (by decide) al_rs1_chain 16 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hR3 hW3 hsz3 hm3 hk3
  have hD3 : WordAt img3 0x440 (Nat.toB256 v) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have hI : ∀ o w, o + 32 ≤ 0x360 → WordAt img o w →
      WordAt (Bytes.writeAt img 0x360 (Bytes.toB256 [1, 64]).toBytes) o w := fun o w ho h => by
    wauto
  have rf0 := cw_restored (hm3 0 (by omega)) (hI _ _ (by decide) hf0)
  have rf1 := cw_restored (hm3 1 (by omega)) (hI _ _ (by decide) hf1)
  have rf2 := cw_restored (hm3 2 (by omega)) (hI _ _ (by decide) hf2)
  have rF := cw_restored (hm3 3 (by omega)) (hI _ _ (by decide) hF)
  have rAF := cw_restored (hm3 4 (by omega)) (hI _ _ (by decide) hAF)
  have rAw := cw_restored (hm3 5 (by omega)) (hI _ _ (by decide) hAw)
  have rT := cw_restored (hm3 8 (by omega)) (hI _ _ (by decide) hT)
  have rb0 := cw_restored (hm3 14 (by omega)) (hI _ _ (by decide) hb0)
  have rb1 := cw_restored (hm3 15 (by omega)) (hI _ _ (by decide) hb1)
  have rb2 := cw_restored (hm3 16 (by omega)) (hI _ _ (by decide) hb2)
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `D0` stored
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x440) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x2e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x2e0 32 = 0x520 by decide] at hsz
  exact k M _ g1 hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)

end Blanc.Lift.Curve3Pool
