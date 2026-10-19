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

/-- **`D0`'s memory, exact**: the save counter at `0x360`, the save of `[0x140, 0x360)`,
`get_D_mem`'s arguments at `0x380 … 0x3e0`, `get_D_mem`'s memory (`getDMemNext`), `D0` parked at
`0x440`, the restore counter, the restore, and `D0` at `0x2e0`. -/
def alD0Mem (M : Mem) (b0 b1 b2 Aw : B256) (x : V3) (v : Nat) : Mem :=
  let M2 := M.write 0x360 (Bytes.toB256 [1, 64]).toBytes
  let M6 := ((((saveMem M2 0x360 0x140 17).write 0x380 b0.toBytes).write 0x3a0 b1.toBytes).write
    0x3c0 b2.toBytes).write 0x3e0 Aw.toBytes
  (restoreMem 0x360 (((getDMemNext M6 (Nat.toB256 (0xff3 + 6)) b0 b1 b2 Aw x v).write 0x440
    (Nat.toB256 v).toBytes).write 0x360 (Bytes.toB256 [3, 64]).toBytes) (0x140 + 32 * 16)
    (exSaved (memWord M2) 0x140 17)).write 0x2e0 (Nat.toB256 v).toBytes

/-- The saved words of a frame save, read off the memory's image, are its words. -/
theorem al_saved_memWord {M : Mem} {img : Bytes} (hR : Mem.Reads M img) :
    (fun o => Bytes.toB256 (img.sliceD o 32 0)) = memWord M := by
  funext o
  unfold memWord
  rw [hR.read]

theorem alD0Mem_eq {Mq1 Mq2 M1 Mq3 Mq4 Mq5 Mq6 M2 Mq7 Mq8 M3 M : Mem} {img2 : Bytes}
    {b0 b1 b2 Aw : B256} {x : V3} {v : Nat}
    (h1 : Mq2 = Mq1.write 864 (Bytes.toB256 [1, 64]).toBytes) (hR2 : Mem.Reads Mq2 img2)
    (hsv : M1 = saveMem Mq2 864 (320 + 32 * 0) (16 + 1))
    (h2 : Mq3 = M1.write 896 b0.toBytes) (h3 : Mq4 = Mq3.write 928 b1.toBytes)
    (h4 : Mq5 = Mq4.write 960 b2.toBytes) (h5 : Mq6 = Mq5.write 992 Aw.toBytes)
    (hg : Mem.EqExcept M2 (getDMemNext Mq6 (Nat.toB256 (4083 + 6)) b0 b1 b2 Aw x v) fun _ => False)
    (h6 : Mq7 = M2.write 1088 (Nat.toB256 v).toBytes)
    (h7 : Mq8 = Mq7.write 864 (Bytes.toB256 [3, 64]).toBytes)
    (hrs : M3 = restoreMem 864 Mq8 (320 + 32 * 16)
      (exSaved (fun o => Bytes.toB256 (img2.sliceD o 32 0)) 320 (16 + 1)))
    (h8 : M = M3.write 736 (Nat.toB256 v).toBytes) :
    Mem.EqExcept M (alD0Mem Mq1 b0 b1 b2 Aw x v) fun _ => False := by
  rw [al_saved_memWord hR2] at hrs
  rw [h8, hrs, h7, h6]
  rw [h5, h4, h3, h2, hsv, h1] at hg
  rw [h1]
  exact eqB_write (((eqB_write (eqB_write hg _ _) _ _).restoreMem 864 _).mono
    fun _ hi => hi.1) _ _

/-- **`D0`, forward, exact** (core of `rx_al_d0`). -/
theorem rx_al_d0E {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
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
      G = g + (2515 + costGetDMem x Aw.toNat) →
      Mem.EqExcept M' (alD0Mem M b0 b1 b2 Aw x v) (fun _ => False) →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_1031_c4 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_0f8f_c0 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 1208 + costGetDMem x Aw.toNat + 28 + 19 + 120 +
      (67 * 16 + 56) + 12 := ⟨G - costGetDMem x Aw.toNat - 2515, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x360) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; have hRq := hR; rw [show memExtSize 0x360 0x360 32 = 0x380 by decide] at hsz
  rw [al_sv1_first]
  refine rx_svFromM (fun o => Bytes.toB256 ((Bytes.writeAt img 0x360
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0x360) (sz := 0x380)
    (by decide) rfl (by decide) (by decide) al_sv1_chain 16 (n := 0) rfl hR hW hsz (by wauto)
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hMsv hR hW hsz hk1 hct1
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
  refine rxe_mstoreL (o := 0x380) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x380 0x380 32 = 0x3a0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := b1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g1') (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x3a0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x3a0 0x3a0 32 = 0x3c0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := b2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH g2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x3c0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0x3c0 0x3c0 32 = 0x3e0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1e0) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH gA) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x3e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x3e0 0x3e0 32 = 0x400 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, ⟨-, hW2, hsz2⟩, hEq2⟩ := getDMem_exact_400L (G := g1 + 1208) (ρ := Nat.toB256 (0xff3 + 6))
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
  refine rxe_mstoreL (o := 0x440) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0x520 0x440 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x360) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0x520 0x360 32 = 0x520 by decide] at hsz
  rw [al_rs1_first]
  refine rx_rsFromM (fun o => Bytes.toB256 ((Bytes.writeAt img 0x360
      (Bytes.toB256 [1, 64]).toBytes).sliceD o 32 0)) (C := 0x360) (sz := 0x520)
    (by decide) rfl (by decide) (by decide) al_rs1_chain 16 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hMrs hR3 hW3 hsz3 hm3 hk3
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
  refine rxe_mstoreL (o := 0x2e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq8; intro M hMq8 hR hW hsz; rw [show memExtSize 0x520 0x2e0 32 = 0x520 by decide] at hsz
  exact k M _ g1 hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega) (by omega)
    (alD0Mem_eq hMq1 hRq hMsv hMq2 hMq3 hMq4 hMq5 hEq2 hMq6 hMq7 hMrs hMq8)

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
    SFunc.RunEx cert.prog sevm (St b S M G) t_0f8f_c0 Q :=
  rx_al_d0E hX hres hR hW hsz hf0 hf1 hf2 hF hAF hAw hT hb0 hb1 hb2 hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

end Blanc.Lift.Curve3Pool
