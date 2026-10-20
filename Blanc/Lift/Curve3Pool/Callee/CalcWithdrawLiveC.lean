import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveB

/-!
# `_calc_withdraw_one_coin`, forward: `D0 = get_D(xp, amp)` and `D1`

`rx_cw_c` (`t_3e2b_c584` → `t_3f41_c984`): the save of `[0x140, 0x420)`, `get_D(xp, amp)`
(`getD_exact`) with `D0` parked at `0x500`, the restore, `D0` at `0x400`, the checked
`D1 = D0 - amount · D0 / supply` at `0x520`, `xp` copied to `0x540 … 0x580` and the next save's
counter at `0x5c0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def cwIdx3 : List Nat := [595, 605, 615, 625, 635, 645, 655, 665, 675, 684, 693, 702, 711, 720,
  729, 738, 747, 757, 767, 776, 785, 794]

def cwIdx4 : List Nat := [803, 812, 821, 830, 839, 848, 857, 866, 875, 884, 893, 902, 911, 920,
  928, 936, 944, 952, 960, 968, 976, 984]

theorem cw_sv2_first : t_3e2b_c584 = svIt 0x04 0x20 0x3e 0x4d (lpBr 22 cwIdx3 0x3e 0x2b t_3e4d_c794 0) :=
  rfl

theorem cw_sv2_chain : ∀ n, n < 22 → cert.prog[cwIdx3.getD n 0]? =
    some (svIt 0x04 0x20 0x3e 0x4d (lpBr 22 cwIdx3 0x3e 0x2b t_3e4d_c794 (n + 1))) := by
  decide +kernel

theorem cw_rs2_first : t_3e9a_c794 = rsIt 0x04 0x20 0x3e 0xbd (lpBr 22 cwIdx4 0x3e 0x9a t_3ebd_c984 0) :=
  rfl

theorem cw_rs2_chain : ∀ n, n < 22 → cert.prog[cwIdx4.getD n 0]? =
    some (rsIt 0x04 0x20 0x3e 0xbd (lpBr 22 cwIdx4 0x3e 0x9a t_3ebd_c984 (n + 1))) := by
  decide +kernel

theorem cw_prog_417 : cert.prog[417]? = some t_04c9_c417 := vk_gd_prog

/-- A restored frame word, read as the word the save saw. -/
theorem cw_restored {img img' : Bytes} {o : Nat} {v : B256}
    (hm : WordAt img' o (Bytes.toB256 (img.sliceD o 32 0))) (h : WordAt img o v) :
    WordAt img' o v := by
  rw [WordAt.eq_self h] at hm
  exact hm

/-- `get_D`'s input memory in `_calc_withdraw_one_coin`: the frame `[0x140, 0x420)` saved
(the counter at `0x420`), `xp` and `amp` at `0x440 … 0x4a0`. -/
def cwCArgs (M : Mem) (x0 x1 x2 Aw : B256) : Mem :=
  ((((saveMem M 0x420 (0x140 + 32 * 0) (22 + 1)).write 0x440 x0.toBytes).write 0x460
    x1.toBytes).write 0x480 x2.toBytes).write 0x4a0 Aw.toBytes

/-- **The memory `rx_cw_c` leaves**, from its entry memory `M`: `get_D`'s result word at `0`
(its scratch is restored over), `D0` parked at `0x500`, the frame restored, then `D0`, `D1`,
`xp` and the next counter. -/
def cwCMem (M : Mem) (x0 x1 x2 Aw D0 a T : B256) : Mem :=
  ((((((restoreMem 0x420 ((((cwCArgs M x0 x1 x2 Aw).write 0 D0.toBytes).write 0x500
    D0.toBytes).write 0x420 (Bytes.toB256 [4, 0]).toBytes) (0x140 + 32 * 22)
    (exSaved (memWord M) 0x140 (22 + 1))).write 0x400 D0.toBytes).write 0x520
    (D0 - a * D0 / T).toBytes).write 0x540 x0.toBytes).write 0x560 x1.toBytes).write 0x580
    x2.toBytes).write 0x5c0 (Bytes.toB256 [1, 64]).toBytes

/-- The restored words and the counter cover a `0x140`-based scratch frame below `hi`. -/
theorem cw_cover {N : Nat} {hi c q : Nat} (ws : List B256) (hws : ws.length = N + 1)
    (hhi : hi ≤ 0x140 + 32 * (N + 1)) (P : Nat → Prop) :
    ∀ i, ¬ ((((0x140 ≤ i ∧ i < hi) ∧ P i) ∧ ¬ (c ≤ i ∧ i < c + q)) ∧
      (ws ≠ [] → ¬ (c ≤ i ∧ i < c + 32)) ∧
      ∀ j, j < ws.length → ¬ (0x140 + 32 * N - 32 * j ≤ i ∧ i < 0x140 + 32 * N - 32 * j + 32)) := by
  rintro i ⟨⟨⟨⟨hi1, hi2⟩, -⟩, -⟩, -, hj⟩
  exact hj (N - (i - 0x140) / 32) (by omega) ⟨by omega, by omega⟩

/-- `rx_cw_cE`'s memory bookkeeping, outside the walk: the actual memory after `get_D`, the
park, the counter, the restore and the stores is `cwCMem`. -/
theorem cwCMem_eq {M M1 M2 M3 : Mem} {img : Bytes} {x0 x1 x2 Aw D0 a T : B256}
    (hR0 : Mem.Reads M img) (hM1 : M1 = saveMem M 0x420 (0x140 + 32 * 0) (22 + 1))
    (hso : ScratchOut ((((M1.write 0x440 x0.toBytes).write 0x460 x1.toBytes).write 0x480
      x2.toBytes).write 0x4a0 Aw.toBytes) M2 0x140 0x340 (Nat.toB256 D0.toNat))
    (hWA : Mem.Wf ((((M1.write 0x440 x0.toBytes).write 0x460 x1.toBytes).write 0x480
      x2.toBytes).write 0x4a0 Aw.toBytes))
    (hszA : ((((M1.write 0x440 x0.toBytes).write 0x460 x1.toBytes).write 0x480
      x2.toBytes).write 0x4a0 Aw.toBytes).size = 0x4c0)
    (hM3 : M3 = restoreMem 0x420 ((M2.write 0x500 (Nat.toB256 D0.toNat).toBytes).write 0x420
      (Bytes.toB256 [4, 0]).toBytes) (0x140 + 32 * 22)
      (exSaved (fun o => Bytes.toB256 (List.sliceD img o 32 0)) 0x140 (22 + 1))) :
    (((((M3.write 0x400 D0.toBytes).write 0x520 (D0 - a * D0 / T).toBytes).write 0x540
      x0.toBytes).write 0x560 x1.toBytes).write 0x580 x2.toBytes).write 0x5c0
      (Bytes.toB256 [1, 64]).toBytes = cwCMem M x0 x1 x2 Aw D0 a T := by
  have hw : (fun o => Bytes.toB256 (List.sliceD img o 32 0)) = memWord M := by
    funext o; unfold memWord; rw [hR0.read]
  rw [toB256_toNat] at hso hM3
  have hg := hso.eqExcept hWA (by rw [hszA]; decide)
  have hr := (((hg.write 0x500 D0.toBytes).write 0x420 (Bytes.toB256 [4, 0]).toBytes).restoreMem
    0x420 (p := 0x140 + 32 * 22) (exSaved (memWord M) 0x140 (22 + 1))).eq
    (cw_cover (N := 22) _ (by rw [exSaved_length]) (by decide) _)
    (Mem.Full.restoreMem _ _ ((Mem.full_write_word_of_grow _ (by
      rw [Mem.size_write_word_of_add_le (by rw [hszA]; decide), hszA]; decide)).write _ _))
    (Mem.Full.restoreMem _ _ ((Mem.full_write_word_of_grow _ (by
      rw [← hso.size] at hszA; rw [hszA]; decide)).write _ _))
  rw [hM3, hw, ← hr]
  unfold cwCMem cwCArgs
  rw [hM1]

/-- **`get_D` and `D1`, forward, exactly** (core). -/
theorem rx_cw_cE {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {x0 x1 x2 a Aw T D0 : B256}
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get Aw.toNat 1 = some D0.toNat)
    (hm : a * D0 / a = D0 ∨ a = 0) (hT0 : T ≠ 0) (hle : ¬ D0 < a * D0 / T)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x440)
    (hctr : WordAt img 0x420 (Nat.toB256 0x140)) (ha : WordAt img 0x140 a)
    (hA : WordAt img 0x1a0 Aw) (hT : WordAt img 0x280 T) (hx0 : WordAt img 0x320 x0)
    (hx1 : WordAt img 0x340 x1) (hx2 : WordAt img 0x360 x2)
    (hG : costGetD x0.toNat x1.toNat x2.toNat Aw.toNat + 3586 + R ≤ G)
    (hroom : S.length + 40 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x5e0 →
      (∀ m v, m < 22 → WordAt img (0x140 + 32 * m) v → WordAt img' (0x140 + 32 * m) v) →
      WordAt img' 0x400 D0 → WordAt img' 0x520 (D0 - a * D0 / T) →
      WordAt img' 0x540 x0 → WordAt img' 0x560 x1 → WordAt img' 0x580 x2 →
      WordAt img' 0x5c0 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      G = g + 3586 + costGetD x0.toNat x1.toNat x2.toNat Aw.toNat →
      M' = cwCMem M x0 x1 x2 Aw D0 a T →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_3f41_c984 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_3e2b_c584 Q := by
  have hR0 := hR
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 1918 + costGetD x0.toNat x1.toNat x2.toNat Aw.toNat + 19 +
      119 + (67 * 22 + 56) := ⟨G - costGetD x0.toNat x1.toNat x2.toNat Aw.toNat - 3586, by omega⟩
  rw [cw_sv2_first]
  refine rx_svFromM (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x420) (sz := 0x440)
    (by decide) rfl (by decide) (by decide) cw_sv2_chain 22 (n := 0) rfl hR hW hsz hctr
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hM1 hR hW hsz hk1 hc1
  -- the arguments of `get_D`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := x0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hx0 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x440) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x440 0x440 32 = 0x460 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := x1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hx1 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreW (o := 0x460) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x460 0x460 32 = 0x480 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x360) (v := x2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hx2 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreW (o := 0x480) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x480 0x480 32 = 0x4a0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1a0) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hA (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x4a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x4a0 0x4a0 32 = 0x4c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x4a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x480) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x440) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hso, hrun⟩ := getD_exact (G := g1 + 1918) (ρ := Nat.toB256 (0x3e88 + 6))
    (S := exSaved (fun o => Bytes.toB256 (img.sliceD o 32 0)) (0x140 + 32 * 0) (22 + 1) ++ S)
    (by rw [hsz]) (by rw [hsz]; decide)
    (by simp only [List.length_append, exSaved_length]; omega) hD0
  refine rxe_pcCall cw_prog_417 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  have hW2 := hso.wf hW
  have hsz2 : M2.size = 0x4c0 := by rw [hso.size, hsz]
  have hsoA := hso
  have hWA := hW
  have hszA := hsz
  clear hR hW hsz hrun hso
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  clear hW2 hsz2
  -- `D0` parked, the restore counter
  obtain ⟨g2, hg2⟩ : ∃ g, g1 + 1918 = g + 293 + (70 * 22 + 59) + 26 := ⟨g1, by omega⟩
  rw [hg2]
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x500) (c := 13) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x4c0 0x500 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x420) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x520 0x420 32 = 0x520 by decide] at hsz
  rw [cw_rs2_first]
  refine rx_rsFromM (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x420) (sz := 0x520)
    (by decide) rfl (by decide) (by decide) cw_rs2_chain 22 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hM3 hR3 hW3 hsz3 hm3 hk3
  have hD : WordAt img3 0x500 (Nat.toB256 D0.toNat) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  rw [toB256_toNat] at hD
  have rha := cw_restored (hm3 0 (by omega)) ha
  have rhT := cw_restored (hm3 10 (by omega)) hT
  have rhx0 := cw_restored (hm3 15 (by omega)) hx0
  have rhx1 := cw_restored (hm3 16 (by omega)) hx1
  have rhx2 := cw_restored (hm3 17 (by omega)) hx2
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `D1`, the copy of `xp`, the next counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x500) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ hD (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x400) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x520 0x400 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x140) (v := a) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rha) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_mulGuard hm) ·)
  -- tree t_3ee5_c984
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x280) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rhT) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_3efb_c984
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hle) ·)
  -- tree t_3f0e_c984
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x520) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x520 0x520 32 = 0x540 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := x0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rhx0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x540) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x540 0x540 32 = 0x560 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := x1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH rhx1) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreW (o := 0x560) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x560 0x560 32 = 0x580 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x360) (v := x2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH rhx2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreW (o := 0x580) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x580 0x580 32 = 0x5a0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x5c0) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x5a0 0x5c0 32 = 0x5e0 by decide] at hsz
  refine k _ _ g2 hR hW hsz (fun m v hm' hv => by wautoH (cw_restored (hm3 m (by omega)) hv))
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)
    (by omega) (cwCMem_eq hR0 hM1 hsoA hWA hszA hM3)


/-- **`get_D` and `D1`, forward.** -/
theorem rx_cw_c {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {x0 x1 x2 a Aw T D0 : B256}
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get Aw.toNat 1 = some D0.toNat)
    (hm : a * D0 / a = D0 ∨ a = 0) (hT0 : T ≠ 0) (hle : ¬ D0 < a * D0 / T)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x440)
    (hctr : WordAt img 0x420 (Nat.toB256 0x140)) (ha : WordAt img 0x140 a)
    (hA : WordAt img 0x1a0 Aw) (hT : WordAt img 0x280 T) (hx0 : WordAt img 0x320 x0)
    (hx1 : WordAt img 0x340 x1) (hx2 : WordAt img 0x360 x2)
    (hG : costGetD x0.toNat x1.toNat x2.toNat Aw.toNat + 3586 + R ≤ G)
    (hroom : S.length + 40 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x5e0 →
      (∀ m v, m < 22 → WordAt img (0x140 + 32 * m) v → WordAt img' (0x140 + 32 * m) v) →
      WordAt img' 0x400 D0 → WordAt img' 0x520 (D0 - a * D0 / T) →
      WordAt img' 0x540 x0 → WordAt img' 0x560 x1 → WordAt img' 0x580 x2 →
      WordAt img' 0x5c0 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_3f41_c984 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_3e2b_c584 Q :=
  rx_cw_cE hD0 hm hT0 hle hR hW hsz hctr ha hA hT hx0 hx1 hx2 hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ _ =>
      k M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end Blanc.Lift.Curve3Pool
