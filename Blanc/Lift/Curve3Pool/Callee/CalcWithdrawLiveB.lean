import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveA

/-!
# `_calc_withdraw_one_coin`, forward: `_xp()` between the first frame save and restore

`rx_cw_b` (`t_3da4_c36` → `t_3e2b_c584`): the save of `[0x140, 0x380)`, `_xp()` (`xp_exact`),
its three words parked at `0x3a0 … 0x3e0`, the restore, and the copy of `xp` to `0x320 … 0x360`
with the next save's counter set at `0x420`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- A computed word offset. -/
theorem cw_off {x y : B256} {o : Nat} (h : x.toNat + y.toNat = o) (ho : o < 2 ^ 256) :
    (x + y).toNat = o := by
  rw [B256.toNat_add, Nat.lo, ← h, Nat.mod_eq_of_lt (by omega)]

/-- A word of an image, read back as itself. -/
theorem wordAt_self (img : Bytes) (o : Nat) : WordAt img o (Bytes.toB256 (img.sliceD o 32 0)) := by
  unfold WordAt
  rw [Bytes.toBytes_toB256_of_length (by rw [List.sliceD_eq_map, List.length_map,
    List.length_range])]

/-- A word an image carries is the word read back. -/
theorem WordAt.eq_self {img : Bytes} {o : Nat} {v : B256} (h : WordAt img o v) :
    Bytes.toB256 (img.sliceD o 32 0) = v := h.read

/-- Across storage loads only. -/
theorem ExLive.sloadsOnly {sevm : Sevm} {W : Devm → Prop} {b b' : Devm} {σ : Stor}
    (h : ExLive sevm W b σ) (hs : SloadsOnly sevm b b') : ExLive sevm W b' σ := by
  induction hs with
  | refl => exact h
  | sload _ k ih => exact ih.sloadE rfl

/-- The first save's iterations after the first. -/
def cwIdx1 : List Nat := [61, 88, 110, 131, 153, 175, 195, 213, 227, 241, 256, 271, 286, 301,
  316, 331, 346]

/-- The first restore's iterations after the first. -/
def cwIdx2 : List Nat := [361, 376, 391, 406, 420, 434, 448, 462, 476, 492, 506, 520, 536, 549,
  562, 573, 584]

theorem cw_sv1_first : t_3da4_c36 = svIt 0x03 0x80 0x3d 0xc6 (lpBr 17 cwIdx1 0x3d 0xa4 t_3dc6_c346 0) :=
  rfl

theorem cw_sv1_chain : ∀ n, n < 17 → cert.prog[cwIdx1.getD n 0]? =
    some (svIt 0x03 0x80 0x3d 0xc6 (lpBr 17 cwIdx1 0x3d 0xa4 t_3dc6_c346 (n + 1))) := by
  decide +kernel

theorem cw_rs1_first : t_3de3_c346 = rsIt 0x03 0x80 0x3e 0x06 (lpBr 17 cwIdx2 0x3d 0xe3 t_3e06_c584 0) :=
  rfl

theorem cw_rs1_chain : ∀ n, n < 17 → cert.prog[cwIdx2.getD n 0]? =
    some (rsIt 0x03 0x80 0x3e 0x06 (lpBr 17 cwIdx2 0x3d 0xe3 t_3e06_c584 (n + 1))) := by
  decide +kernel

theorem cw_prog_31 : cert.prog[31]? = some t_0281_c31 := vk_xp_prog

/-- The bytes `_xp` may leave changed outside the frames `_calc_withdraw_one_coin` restores: its
mapping key word at `0xc0`. -/
def cwD : Nat → Prop := fun i => 0xc0 ≤ i ∧ i < 0xe0

/-- **The memory `rx_cw_b` leaves**, off `cwD`, from its entry memory `M`: the frame
`[0x140, 0x380)` saved, `xp` parked at `0x3a0 … 0x3e0`, the frame restored, `xp` copied to
`0x320 … 0x360` and the next counter at `0x420`. -/
def cwBMem (M : Mem) (x0 x1 x2 : B256) : Mem :=
  ((((restoreMem 0x380 (((((saveMem M 0x380 (0x140 + 32 * 0) (17 + 1)).write 0x3a0
    x0.toBytes).write 0x3c0 x1.toBytes).write 0x3e0 x2.toBytes).write 0x380
    (Bytes.toB256 [3, 96]).toBytes) (0x140 + 32 * 17) (exSaved (memWord M) 0x140 (17 + 1))).write
    0x320 x0.toBytes).write 0x340 x1.toBytes).write 0x360 x2.toBytes).write 0x420
    (Bytes.toB256 [1, 64]).toBytes

/-- `rx_cw_bE`'s memory bookkeeping, outside the walk: off `cwD` the memory is `cwBMem`, and it
is fully materialised (the park at `0x3a0` grows it). -/
theorem cwBMem_eq {M M1 M2 M3 : Mem} {img : Bytes} {x0 x1 x2 : B256}
    (hR0 : Mem.Reads M img) (hM1 : M1 = saveMem M 0x380 (0x140 + 32 * 0) (17 + 1))
    (hkx : Mem.KeepsOff M1 M2 xpWin) (hW1 : Mem.Wf M1) (hsz1 : M1.size = 0x3a0)
    (hW2 : Mem.Wf M2) (hsz2 : M2.size = 0x3a0)
    (hM3 : M3 = restoreMem 0x380 ((((M2.write 0x3a0 x0.toBytes).write 0x3c0 x1.toBytes).write
      0x3e0 x2.toBytes).write 0x380 (Bytes.toB256 [3, 96]).toBytes) (0x140 + 32 * 17)
      (exSaved (fun o => Bytes.toB256 (List.sliceD img o 32 0)) 0x140 (17 + 1))) :
    Mem.EqExcept ((((M3.write 0x320 x0.toBytes).write 0x340 x1.toBytes).write 0x360
      x2.toBytes).write 0x420 (Bytes.toB256 [1, 64]).toBytes) (cwBMem M x0 x1 x2) cwD ∧
    Mem.Full ((((M3.write 0x320 x0.toBytes).write 0x340 x1.toBytes).write 0x360
      x2.toBytes).write 0x420 (Bytes.toB256 [1, 64]).toBytes) := by
  have hw : (fun o => Bytes.toB256 (List.sliceD img o 32 0)) = memWord M := by
    funext o; unfold memWord; rw [hR0.read]
  rw [hw] at hM3
  have hg := (hkx.eqExcept (hsz2.trans hsz1.symm) hW1 hW2).symm
  have h2 := (((((((((hg.write 0x3a0 x0.toBytes).write 0x3c0 x1.toBytes).write 0x3e0
    x2.toBytes).write 0x380 (Bytes.toB256 [3, 96]).toBytes).restoreMem 0x380
    (p := 0x140 + 32 * 17) (exSaved (memWord M) 0x140 (17 + 1))).write 0x320 x0.toBytes).write
    0x340 x1.toBytes).write 0x360 x2.toBytes).write 0x420 (Bytes.toB256 [1, 64]).toBytes)
  refine ⟨?_, ?_⟩
  · rw [hM3]
    unfold cwBMem
    rw [← hM1]
    refine h2.mono fun i hi => ?_
    have h0 := hi.1.1.1.1.1.1.1.1.1
    have hj := hi.1.1.1.1.2.2
    simp only [Mem.OffWindows, xpWin, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, not_and_or, not_or, not_lt] at h0
    unfold cwD
    rcases h0 with h0 | h0
    · omega
    · exact absurd ⟨by omega, by omega⟩ (hj (17 - (i - 0x140) / 32) (by rw [exSaved_length]; omega))
  · rw [hM3]
    exact ((((Mem.Full.restoreMem _ _ ((((Mem.full_write_word_of_grow _ (by rw [hsz2]; decide)).write
      _ _).write _ _).write _ _)).write _ _).write _ _).write _ _).write _ _

/-- **`_xp()` between the first frame save and restore, forward, exactly** (core): the
continuation also receives the exact charge and the memory, equal to `cwBMem` off `_xp`'s key
word `0xc0` (`cwD`), fully materialised. -/
theorem rx_cw_bE {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {W : Devm → Prop} {x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3a0)
    (hctr : WordAt img 0x380 (Nat.toB256 0x140))
    (hG : xpGas sevm b + 2585 + R ≤ G) (hroom : S.length + 40 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x440 →
      (∀ m v, m < 15 → WordAt img (0x140 + 32 * m) v → WordAt img' (0x140 + 32 * m) v) →
      WordAt img' 0x320 x0 → WordAt img' 0x340 x1 → WordAt img' 0x360 x2 →
      WordAt img' 0x420 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      G = g + 2585 + xpGas sevm b → b' = xpBase sevm b →
      Mem.EqExcept M' (cwBMem M x0 x1 x2) cwD → Mem.Full M' →
      SFunc.RunEx cert.prog sevm (St b' S M' g) t_3e2b_c584 Q) :
    SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x03, 0x20] :: S) M G) t_3da4_c36 Q := by
  have hR0 := hR
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 1370 + xpGas sevm b + 20 + (67 * 17 + 56) :=
    ⟨G - xpGas sevm b - 1390 - (67 * 17 + 56), by omega⟩
  rw [cw_sv1_first]
  refine rx_svFromM (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x380) (sz := 0x3a0)
    (by decide) rfl (by decide) (by decide) cw_sv1_chain 17 (n := 0) rfl hR hW hsz hctr
    (fun m _ _ => wordAt_self _ _) (by simp only [List.length_cons]; omega) ?_
  intro M1 img1 hM1 hR1 hW1 hsz1 hk1 hc1
  clear hR hW hsz
  -- `_xp()`
  have ha' : Abstracts (b.getStor sevm.currentTarget) s := ha.of_lock fun x _ => hL.stor x
  obtain ⟨y0, y1, y2, ⟨M2, hrun, hkx, hW2, hsz2⟩, hy⟩ := xp_exact (G := g1 + 1370)
    (ret := Nat.toB256 (0x3dc9 + 6)) (S := exSaved (fun o => Bytes.toB256 (img.sliceD o 32 0))
      (0x140 + 32 * 0) (17 + 1) ++ Bytes.toB256 [0x03, 0x20] :: S) hfork ha' hX hW1 hsz1
    (by decide) (by decide) (by simp only [List.length_append, exSaved_length, List.length_cons]; omega)
  obtain ⟨rfl, rfl, rfl⟩ : x0 = y0 ∧ x1 = y1 ∧ x2 = y2 := by
    simp only [V3.mk.injEq] at hy
    exact ⟨B256.toNat_inj _ _ hy.1, B256.toNat_inj _ _ hy.2.1, B256.toNat_inj _ _ hy.2.2⟩
  xr (rx_dest ·)
  refine rxe_pcCall cw_prog_31 (by decide)
    (by simp only [List.length_append, exSaved_length, List.length_cons]; omega) hrun ?_
  have hL2 := hL.sloadsOnly (xpBase_sloadsOnly sevm b)
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  have hWX1 := hW1
  have hszX1 := hsz1
  have hWX2 := hW2
  have hszX2 := hsz2
  clear hR1 hW1 hsz1 hrun hW2 hsz2
  -- the words parked, the restore counter
  obtain ⟨g2, hg2⟩ : ∃ g, g1 + 1370 = g + 1332 + 38 := ⟨g1, by omega⟩
  rw [hg2]
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x3a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3a0 0x3a0 32 = 0x3c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x3c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3c0 0x3c0 32 = 0x3e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x3e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3e0 0x3e0 32 = 0x400 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x380) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x400 0x380 32 = 0x400 by decide] at hsz
  -- the restore
  rw [cw_rs1_first, show g2 + 1332 = g2 + 83 + 70 * 17 + 59 by omega]
  refine rx_rsFromM (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x380) (sz := 0x400)
    (by decide) rfl (by decide) (by decide) cw_rs1_chain 17 (n := 0) rfl hR hW hsz
    (by wauto) (by simp only [List.length_cons]; omega) ?_
  intro M3 img3 hM3 hR3 hW3 hsz3 hm3 hk3
  have hx0 : WordAt img3 0x3a0 x0 := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have hx1 : WordAt img3 0x3c0 x1 := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have hx2 : WordAt img3 0x3e0 x2 := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- the copy of `xp`, the next counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x3a0) hR hsz rfl (by decide) hx0 (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x320) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x400 0x320 32 = 0x400 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x3c0) hR hsz (by decide) (by decide) (hx1.write_other (by simp only [B256.length_toBytes]; omega)) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreW (o := 0x340) (c := 3) hR hW hsz (by decide) (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x400 0x340 32 = 0x400 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x3e0) hR hsz (by decide) (by decide) ((hx2.write_other (by simp only [B256.length_toBytes]; omega)).write_other (by simp only [B256.length_toBytes]; omega)) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreW (o := 0x360) (c := 3) hR hW hsz (by decide) (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x400 0x360 32 = 0x400 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreW (o := 0x420) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x400 0x420 32 = 0x440 by decide] at hsz
  refine k _ _ _ g2 hL2 hR hW hsz (fun m v hm hv => by
      have e := hm3 m (by omega)
      rw [WordAt.eq_self hv] at e
      exact (((e.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega) (by omega) rfl
    (cwBMem_eq hR0 hM1 hkx hWX1 hszX1 hWX2 hszX2 hM3).1
    (cwBMem_eq hR0 hM1 hkx hWX1 hszX1 hWX2 hszX2 hM3).2

/-- **`_xp()` between the first frame save and restore, forward.** -/
theorem rx_cw_b {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {W : Devm → Prop} {x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3a0)
    (hctr : WordAt img 0x380 (Nat.toB256 0x140))
    (hG : xpGas sevm b + 2585 + R ≤ G) (hroom : S.length + 40 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x440 →
      (∀ m v, m < 15 → WordAt img (0x140 + 32 * m) v → WordAt img' (0x140 + 32 * m) v) →
      WordAt img' 0x320 x0 → WordAt img' 0x340 x1 → WordAt img' 0x360 x2 →
      WordAt img' 0x420 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' S M' g) t_3e2b_c584 Q) :
    SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x03, 0x20] :: S) M G) t_3da4_c36 Q :=
  rx_cw_bE hfork hL ha hX hR hW hsz hctr hG hroom
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _ _ _ _ =>
      k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

end Blanc.Lift.Curve3Pool
