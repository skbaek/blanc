import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPre

/-!
# `add_liquidity`, part 3: `D0`

From the supply test (`0xf83`) to `0x1031`: when `token_supply > 0`, `D0 = get_D_mem(old, amp)`
with the frame save and restore around the call; otherwise `D0 = 0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- `add_liquidity`'s words before the pull loop: `fees` zero, `_fee`, `_admin_fee`, `amp`,
`token_supply`, `D0` and `old_balances`. -/
structure AlMem0 (img : Bytes) (F AF A T D0 : B256) (old : Nat → B256) : Prop where
  f0 : WordAt img 0x140 0
  f1 : WordAt img 0x160 0
  f2 : WordAt img 0x180 0
  fee : WordAt img 0x1a0 F
  adm : WordAt img 0x1c0 AF
  amp : WordAt img 0x1e0 A
  supply : WordAt img 0x240 T
  d0 : WordAt img 0x2e0 D0
  o0 : WordAt img 0x300 (old 0)
  o1 : WordAt img 0x320 (old 1)
  o2 : WordAt img 0x340 (old 2)

theorem al_restored {src img : Bytes} {o : Nat} {w : B256}
    (h : WordAt img o (Bytes.toB256 (src.sliceD o 32 0))) (hs : WordAt src o w) : WordAt img o w := by
  rw [hs.read] at h; exact h

/-- **`D0`** (`0xf83` → `0x1031`). -/
theorem xa_al_p3 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T : B256} {old : Nat → B256}
    (hchk : Cert.CheckedM code cert mems true) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0) (hm : AlMem0 img F AF A T 0 old)
    (h : XAt sevm post 0xf83 (St b [] M G) L) :
    ∃ (D0 : B256) (M' : Mem) (img' : Bytes) (G' : Nat), Mem.Reads M' img' ∧ Mem.Wf M' ∧
      M'.size % 32 = 0 ∧ AlMem0 img' F AF A T D0 old ∧ (T = 0 → D0 = 0) ∧
      (T ≠ 0 → getDMem ⟨(old 0).toNat, (old 1).toNat, (old 2).toNat⟩ A.toNat = some D0.toNat) ∧
      XAt sevm post 0x1031 (St b [] M' G') L := by
  xs 0xf85 (.push [0x00] (by decide)) ri_push
  xs 0xf88 (.push [0x02, 0x40] (by decide)) ri_push
  xml 0xf89 0x240 hm.supply
  xs 0xf8a (.reg .gt) ri_gt
  xs 0xf8b (.reg .iszero) ri_iszero
  xs 0xf8e (.push [0x10, 0x31] (by decide)) ri_push
  xji 0xf8f 0x1031 hw
  · have hT : T ≠ 0 := by
      have e := gtCheck_ne_zero (eqCheck_eq_zero hw)
      intro hT0; rw [hT0] at e; exact absurd e (by decide)
    clear hw
    xs 0xf92 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0xf95 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xf96 (.reg .mstore) (ri_mstore_imgAtA (o := 0x360) rfl)
    obtain ⟨M1, img1, G1, hR1, hW1, hA1, hk1, h⟩ := xa_al_save1 hcode 16 0 [] _ _ _ rfl hR hW hA
      (by rw [show Nat.toB256 (0x140 + 32 * 0) = Bytes.toB256 [0x01, 0x40] by decide]
          exact WordAt.write_self _ _ _) h
    clear hR hW hA
    have g : ∀ o w, WordAt img o w → (o + 32 ≤ 0x360 ∨ 0x380 ≤ o) → WordAt img1 o w :=
      fun o w hw ho => hk1 o w (hw.write_other (by simp only [B256.length_toBytes]; omega)) ho
    have hR := hR1
    have hW := hW1
    have hA := hA1
    clear hR1 hW1 hA1
    xjd 0xfb9
    xs 0xfbc (.push [0x03, 0x80] (by decide)) ri_push
    xs 0xfbf (.push [0x03, 0x00] (by decide)) ri_push
    xs 0xfc0 (.reg (.dup 0)) (ri_dup (by rfl))
    xml 0xfc1 0x300 (g _ _ hm.o0 (by decide))
    xs 0xfc2 (.reg (.dup 2)) (ri_dup (by rfl))
    xma 0xfc3 (.reg .mstore) (ri_mstore_imgAtA (o := 0x380) rfl)
    xs 0xfc4 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0xfc6 (.push [0x20] (by decide)) ri_push
    xs 0xfc7 (.reg .add) ri_add
    xml 0xfc8 0x320 (g _ _ hm.o1 (by decide))
    xs 0xfc9 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0xfcb (.push [0x20] (by decide)) ri_push
    xs 0xfcc (.reg .add) ri_add
    xma 0xfcd (.reg .mstore) (ri_mstore_imgAtA (o := 0x3a0) rfl)
    xs 0xfce (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0xfd0 (.push [0x40] (by decide)) ri_push
    xs 0xfd1 (.reg .add) ri_add
    xml 0xfd2 0x340 (g _ _ hm.o2 (by decide))
    xs 0xfd3 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0xfd5 (.push [0x40] (by decide)) ri_push
    xs 0xfd6 (.reg .add) ri_add
    xma 0xfd7 (.reg .mstore) (ri_mstore_imgAtA (o := 0x3c0) rfl)
    xs 0xfd8 (.reg .pop) ri_pop
    xs 0xfd9 (.reg .pop) ri_pop
    xs 0xfdc (.push [0x01, 0xe0] (by decide)) ri_push
    xml 0xfdd 0x1e0 (g _ _ hm.amp (by decide))
    xs 0xfe0 (.push [0x03, 0xe0] (by decide)) ri_push
    xma 0xfe1 (.reg .mstore) (ri_mstore_imgAtA (o := 0x3e0) rfl)
    xs 0xfe4 (.push [0x03, 0xe0] (by decide)) ri_push
    xml 0xfe5 0x3e0 (WordAt.write_self _ _ _)
    xs 0xfe8 (.push [0x03, 0xc0] (by decide)) ri_push
    xml 0xfe9 0x3c0 (WordAt.write_self _ _ _)
    xs 0xfec (.push [0x03, 0xa0] (by decide)) ri_push
    xml 0xfed 0x3a0 (WordAt.write_self _ _ _)
    xs 0xff0 (.push [0x03, 0x80] (by decide)) ri_push
    xml 0xff1 0x380 (WordAt.write_self _ _ _)
    xs 0xff3 (.push [0x06] (by decide)) ri_push
    replace h := xa_al_pc (atN hcode (by kernel_rfl)) h
    obtain ⟨_, h⟩ := h
    xs 0xff5 (.reg .add) ri_add
    rw [show Nat.toB256 0xff3 + Bytes.toB256 [6] = Nat.toB256 0xff9 by decide] at h
    xs 0xff8 (.push [0x07, 0xb7] (by decide)) ri_push
    xjmp 0x7b7
    obtain ⟨v, M2, G2, hv, hk, hW2, hA2, h⟩ := xa_al_getDMem hchk hcode hfork hW hA h
    rw [show (Nat.toB256 0xff9).toNat = 0xff9 by decide] at h
    obtain ⟨img2, hR2, -⟩ := Mem.Reads.keepsOff hR hk
    clear hR hW hA hk
    have hR := hR2
    have hW := hW2
    have hA := hA2
    clear hR2 hW2 hA2
    xjd 0xffa
    xs 0xffd (.push [0x04, 0x40] (by decide)) ri_push
    xma 0xffe (.reg .mstore) (ri_mstore_imgAtA (o := 0x440) rfl)
    xs 0x1001 (.push [0x03, 0x40] (by decide)) ri_push
    xs 0x1004 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x1005 (.reg .mstore) (ri_mstore_imgAtA (o := 0x360) rfl)
    replace h : XAt sevm post 0x1005 (St b (svWords (Bytes.writeAt img 0x360
      (Bytes.toB256 [0x01, 0x40]).toBytes) 0x140 (16 + 1) ++ []) _ _) L := h
    obtain ⟨M3, img3, G3, hR3, hW3, hA3, hj, hk3, h⟩ := xa_al_restore1 hcode 16 [] _ _ _
      (by omega) hR hW hA
      (by rw [show Nat.toB256 (0x140 + 32 * 16) = Bytes.toB256 [0x03, 0x40] by decide]
          exact WordAt.write_self _ _ _) h
    clear hR hW hA
    have hR := hR3
    have hW := hW3
    have hA := hA3
    clear hR3 hW3 hA3
    xjd 0x1029
    xs 0x102c (.push [0x04, 0x40] (by decide)) ri_push
    xml 0x102d 0x440 (hk3 _ _ ((WordAt.write_self _ _ _).write_other
      (by simp only [B256.length_toBytes]; omega)) (by omega) (by omega))
    xs 0x1030 (.push [0x02, 0xe0] (by decide)) ri_push
    xma 0x1031 (.reg .mstore) (ri_mstore_imgAtA (o := 0x2e0) rfl)
    have r : ∀ j o w, j ≤ 16 → 0x140 + 32 * j = o → WordAt img o w → WordAt img3 o w :=
      fun j o w hj' e hw => by
        subst e
        exact al_restored (hj j hj') (hw.write_other (by simp only [B256.length_toBytes]; omega))
    have wo : ∀ o w, WordAt img3 o w → (o + 32 ≤ 0x2e0 ∨ 0x300 ≤ o) →
        WordAt (Bytes.writeAt img3 0x2e0 v.toBytes) o w :=
      fun o w hw ho => hw.write_other (by simp only [B256.length_toBytes]; omega)
    refine ⟨v, M, _, _, hR, hW, hA, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, WordAt.write_self _ _ _, ?_, ?_, ?_⟩,
      fun e => absurd e hT, fun _ => hv, h⟩
    · exact wo _ _ (r 0 _ _ (by decide) (by decide) hm.f0) (by decide)
    · exact wo _ _ (r 1 _ _ (by decide) (by decide) hm.f1) (by decide)
    · exact wo _ _ (r 2 _ _ (by decide) (by decide) hm.f2) (by decide)
    · exact wo _ _ (r 3 _ _ (by decide) (by decide) hm.fee) (by decide)
    · exact wo _ _ (r 4 _ _ (by decide) (by decide) hm.adm) (by decide)
    · exact wo _ _ (r 5 _ _ (by decide) (by decide) hm.amp) (by decide)
    · exact wo _ _ (r 8 _ _ (by decide) (by decide) hm.supply) (by decide)
    · exact wo _ _ (r 14 _ _ (by decide) (by decide) hm.o0) (by decide)
    · exact wo _ _ (r 15 _ _ (by decide) (by decide) hm.o1) (by decide)
    · exact wo _ _ (r 16 _ _ (by decide) (by decide) hm.o2) (by decide)
  · have hT : T = 0 := by
      have e := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 by decide] at e
      exact B256.toNat_inj _ _ (by rw [show (0 : B256).toNat = 0 from rfl]; omega)
    exact ⟨0, M, img, _, hR, hW, hA, hm, fun _ => rfl, fun e => absurd hT e, h⟩

end Blanc.Lift.Curve3Pool
