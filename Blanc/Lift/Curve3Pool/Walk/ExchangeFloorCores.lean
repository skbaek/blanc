import Blanc.Lift.ExactCallFloor
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFrame
import Blanc.Lift.Curve3Pool.ExchangeExactSchedule

/-!
# `exchange`'s stage cores at the true gas minimum

`rx_ex_pre_coreF`, `rx_ex_store_coreF`, `rx_ex_pull_coreF`, `rx_ex_push_coreF` are `rx_ex_pre_core` and its siblings
with their constant budgets gone: each storage step is admitted on its own charge (`rxe_sloadVE`, `rxe_sstoreVE`),
each coin call on its floor (`MutableFloorProfile`). The other stages' demands are small constants, which the
frame's later charges cover, so the existing cores serve.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- `SLOAD` at its own charge. -/
theorem rxe_sloadVE {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f : SFunc}
    {Q : Outcome → Prop} {k' : B256} (hfork : ShanghaiOnwards sevm.benvStat.fork)
    (hroom : S.length < 1024) (hG : sloadCost sevm b k' ≤ G)
    (k : ∀ G' b' v, b' = afterSload sevm b k' → v = b.getStorVal sevm.currentTarget k' →
      G' ≤ G → G = G' + sloadCost sevm b k' →
      SFunc.RunEx fs sevm (St b' (v :: S) M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: S) M G) (.next (.reg .sload) f) Q := by
  obtain ⟨r, hr, hq⟩ := k (G - sloadCost sevm b k') _ _ rfl rfl (by omega) (by omega)
  refine ⟨r, ?_, hq⟩
  rw [show G = (G - sloadCost sevm b k') + sloadCost sevm b k' by omega]
  exact rx_sload_sel hfork hroom hr

/-- `SSTORE` at its own charge, above the sentry. -/
theorem rxe_sstoreVE {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f : SFunc}
    {Q : Outcome → Prop} {k' v : B256} (hfork : ShanghaiOnwards sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hG : sstoreCost sevm b k' v ≤ G) (hs : gCallStipend < G)
    (k : ∀ G' b', b' = afterSstore sevm b k' v → G' ≤ G → G = G' + sstoreCost sevm b k' v →
      SFunc.RunEx fs sevm (St b' S M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: v :: S) M G) (.next (.reg .sstore) f) Q := by
  obtain ⟨r, hr, hq⟩ := k (G - sstoreCost sevm b k' v) _ rfl (by omega) (by omega)
  refine ⟨r, ?_, hq⟩
  rw [show G = (G - sstoreCost sevm b k' v) + sstoreCost sevm b k' v by omega]
  exact rx_sstore hfork (by omega) hstatic hr

theorem rx_ex_pre_coreF {sevm : Sevm} {b0 b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} (hfork : ShanghaiOnwards sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hB : ExBase sevm b0 b σ) (hWc : WClosed sevm W)
    (hWb : W b) (hlock : σ.get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : σ.get isKilledSlot = 0) (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0) (hcl : VyClamps img)
    (hG : G = R + 661 + exPreCost sevm b) (hR0 : 2301 ≤ R)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (z0 z1 z2 : B256),
      ExBase sevm b0 b1 (σ.set lockSlot 1) → W b1 → Mem.Reads M1 img1 → Mem.Wf M1 →
      M1.size = 0x2e0 →
      G = g + 661 + exPreCost sevm b → b1 = exPreBase sevm b → M1 = exPreMem M σ →
      z0 = Bytes.toB256 (img.sliceD 0x200 32 0) → z1 = Bytes.toB256 (img.sliceD 0x220 32 0) →
      z2 = Bytes.toB256 (img.sliceD 0x240 32 0) →
      SFunc.RunEx cert.prog sevm (St b1 [balAt σ 0, balAt σ 1, balAt σ 2, z2, z1, z0,
        balAt σ 2, balAt σ 1, balAt σ 0, exR1, exR1, exR0, Bytes.toB256 [2, 0]] M1 g)
        (pcCallTree 0x2452 0x03 0xa1 34 t_2458_c0) Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2319_c0 Q := by
  have e40 : Bytes.toB256 (img.sliceD 64 32 0) = Bytes.toB256 vyC40 := by
    rw [hcl.2.1, B256.toB256_toBytes]
  have e60 : Bytes.toB256 (img.sliceD 96 32 0) = Bytes.toB256 vyC60 := by
    rw [hcl.2.2.1, B256.toB256_toBytes]
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3 := ⟨G - 3, by omega⟩
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVE hfork (by hr) (by unfold exPreCost at hG; omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hx_g2
  have hc2 : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm (afterSstore sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15]) + sloadCost sevm (afterSload sevm (afterSstore sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])) balancesBase +
      sloadCost sevm (afterSload sevm (afterSload sevm (afterSstore sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])) balancesBase) (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm (afterSload sevm (afterSload sevm (afterSload sevm (afterSstore sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])) balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2]) := by
    rw [hb2]; rfl
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 23 := ⟨g2 - 23, by omega⟩
  wrun 2
  xr (rx_branch_succ (by rw [hv2, getStorVal_eq, lockSlot_lit, hB.stor, hlock]; decide) ·)
  -- tree t_2327_c0
  wrun 3
  refine rxe_sstoreVE hfork hstatic (by omega) (by simp only [gCallStipend]; omega) ?_; intro g4 b4 hb4 hg41 hx_g4
  have hc4 : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm b4 (Bytes.toB256 [15]) + sloadCost sevm (afterSload sevm b4 (Bytes.toB256 [15])) balancesBase +
      sloadCost sevm (afterSload sevm (afterSload sevm b4 (Bytes.toB256 [15])) balancesBase) (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm (afterSload sevm (afterSload sevm (afterSload sevm b4 (Bytes.toB256 [15])) balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2]) := by
    rw [hb4, hb2]; rfl
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 172 := ⟨g4 - 172, by omega⟩
  wrun 3
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  -- tree t_2339_c0
  wrun 2
  xr (rxm_mload (o := 0x60) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 4
  xr (rxm_mload (o := 0x40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 4
  xr (rx_branch_succ (by rw [e40]; exact ex_clamp_hi hi) ·)
  -- tree t_234f_c0
  wrun 7
  xr (rx_branch_succ (by rw [e60]; exact ex_clamp_lo hi) ·)
  -- tree t_235d_c0
  wrun 3
  xr (rxm_mload (o := 0x60) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 4
  xr (rxm_mload (o := 0x40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 4
  xr (rx_branch_succ (by rw [e40]; exact ex_clamp_hi hj) ·)
  -- tree t_2374_c0
  wrun 7
  xr (rx_branch_succ (by rw [e60]; exact ex_clamp_lo hj) ·)
  -- tree t_2382_c0
  wrun 3
  refine rxe_sloadVE hfork (by hr) (by omega) ?_; intro g6 b6 v6 hb6 hv6 hg61 hx_g6
  have hc6 : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm b4 (Bytes.toB256 [15]) + sloadCost sevm b6 balancesBase +
      sloadCost sevm (afterSload sevm b6 balancesBase) (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm (afterSload sevm (afterSload sevm b6 balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2]) := by
    rw [hb6, hb4, hb2]; rfl
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 139 := ⟨g6 - 139, by omega⟩
  wrun 2
  xr (rx_branch_succ (by rw [hv6, hb4, hb2, isKilledSlot_lit, getStorVal_afterSstore_ne (by decide), getStorVal_afterSload, getStorVal_eq, hB.stor, hkill]; decide) ·)
  -- tree t_2390_c0
  wrun 4
  refine rxe_mstoreW (o := 0x140) (c := 18) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xc0 0x140 32 = 0x160 by decide] at hsz
  wrun 4
  refine rxe_mstoreW (o := 0x160) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x160 0x160 32 = 0x180 by decide] at hsz
  wrun 4
  refine rxe_mstoreW (o := 0x180) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x180 0x180 32 = 0x1a0 by decide] at hsz
  wrun 5
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1a0 0xc0 32 = 0x1a0 by decide] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  refine rxe_sloadVE hfork (by hr) (by omega) ?_; intro g8 b8 v8 hb8 hv8 hg81 hx_g8
  have hc8 : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm b4 (Bytes.toB256 [15]) + sloadCost sevm b6 balancesBase +
      sloadCost sevm b8 (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm (afterSload sevm b8 (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2]) := by
    rw [hb8, hb6, hb4, hb2]; rfl
  obtain ⟨g9, rfl⟩ : ∃ g, g8 = g + 66 := ⟨g8 - 66, by omega⟩
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x1a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1a0 0x1a0 32 = 0x1c0 by decide] at hsz
  wrun 3
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1c0 0xc0 32 = 0x1c0 by decide] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sloadVE hfork (by hr) (by omega) ?_; intro g10 b10 v10 hb10 hv10 hg101 hx_g10
  have hc10 : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm b4 (Bytes.toB256 [15]) + sloadCost sevm b6 balancesBase +
      sloadCost sevm b8 (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm b10 (balancesBase + Bytes.toB256 [2]) := by
    rw [hb10, hb8, hb6, hb4, hb2]; rfl
  obtain ⟨g11, rfl⟩ : ∃ g, g10 = g + 72 := ⟨g10 - 72, by omega⟩
  wrun 3
  refine rxe_mstoreW (o := 0x1c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1c0 0x1c0 32 = 0x1e0 by decide] at hsz
  wrun 3
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1e0 0xc0 32 = 0x1e0 by decide] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sloadVE hfork (by hr) (by omega) ?_; intro g12 b12 v12 hb12 hv12 hg121 hx_g12
  obtain ⟨g13, rfl⟩ : ∃ g, g12 = g + 186 := ⟨g12 - 186, by omega⟩
  wrun 3
  refine rxe_mstoreW (o := 0x1e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1e0 0x1e0 32 = 0x200 by decide] at hsz
  wrun 4
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x180) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  refine rxe_mloadXL (o := 0x200) (c := 6) hR hW hsz rfl (by decide) (by hr) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x200 0x200 32 = 0x220 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mloadXL (o := 0x220) (c := 6) hR hW hsz rfl (by decide) (by hr) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x220 0x220 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mloadXL (o := 0x240) (c := 6) hR hW hsz rfl (by decide) (by hr) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x240 0x240 32 = 0x260 by decide] at hsz
  wrun 3
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x280) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x260 0x280 32 = 0x2a0 by decide] at hsz
  wrun 3
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 3
  refine rxe_mstoreW (o := 0x2a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x2a0 0x2a0 32 = 0x2c0 by decide] at hsz
  wrun 3
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 3
  refine rxe_mstoreW (o := 0x2c0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x2c0 0x2c0 32 = 0x2e0 by decide] at hsz
  wrun 3
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x280) hR hsz rfl (by decide) (by hr) ·); try wsimp
  have hB4 : ExBase sevm b0 b4 (σ.set lockSlot 1) := by
    rw [hb4, hb2, lockSlot_lit, show Bytes.toB256 [1] = (1 : B256) by decide]
    exact (hB.sloadP _).sstore _ _
  have hW4 : W b4 := by rw [hb4, hb2]; exact hWc.sstore _ _ _ (hWc.sload _ _ hWb)
  have hB12 : ExBase sevm b0 b12 (σ.set lockSlot 1) := by
    rw [hb12, hb10, hb8, hb6]; exact (((hB4.sloadP _).sloadP _).sloadP _).sloadP _
  have hW12 : W b12 := by
    rw [hb12, hb10, hb8, hb6]
    exact hWc.sload _ _ (hWc.sload _ _ (hWc.sload _ _ (hWc.sload _ _ hW4)))
  have e8 : v8 = balAt σ 0 := by
    rw [hv8, getStorVal_eq, hb6, afterSload_getStor, hB4.stor, Stor.get_set_ne _ (by decide)]
    rfl
  have e10 : v10 = balAt σ 1 := by
    rw [hv10, getStorVal_eq, hb8, afterSload_getStor, hb6, afterSload_getStor, hB4.stor,
      Stor.get_set_ne _ (by decide)]
    rfl
  have e12 : v12 = balAt σ 2 := by
    rw [hv12, getStorVal_eq, hb10, afterSload_getStor, hb8, afterSload_getStor, hb6,
      afterSload_getStor, hB4.stor, Stor.get_set_ne _ (by decide)]
    rfl
  rw [e8, e10, e12] at hR hW hsz ⊢
  have hc : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm b4 (Bytes.toB256 [15]) + sloadCost sevm b6 balancesBase +
      sloadCost sevm b8 (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm b10 (balancesBase + Bytes.toB256 [2]) := by
    rw [hb10, hb8, hb6, hb4, hb2]; rfl
  refine k b12 _ _ g13 _ _ _ hB12 hW12 hR hW hsz (by omega) ?_ rfl rfl rfl
    rfl
  rw [hb12, hb10, hb8, hb6, hb4, hb2]; rfl


theorem rx_ex_store_coreF {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C dyOut dyFee : B256}
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa00)
    (hF : ExFrame img B X D C) (hout : WordAt img 0x920 dyOut) (hfee : WordAt img 0x940 dyFee)
    (hma : dyFee * σ.get adminFeeSlot / dyFee = σ.get adminFeeSlot ∨ dyFee = 0)
    (hmap : exAdm0 dyFee (σ.get adminFeeSlot) * exR0 / exAdm0 dyFee (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 dyFee (σ.get adminFeeSlot) = 0)
    (hbi : ¬ B (exI sevm).toNat + D < B (exI sevm).toNat)
    (hbj1 : ¬ B (exJ sevm).toNat < dyOut)
    (hbj2 : ¬ B (exJ sevm).toNat - dyOut <
      exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))
    (hG : G = R + 1225 + exStoreCost sevm b (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)))
    (hR0 : 2301 ≤ R) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' ((σ.set (balancesBase + exI sevm) (B (exI sevm).toNat + D)).set
        (balancesBase + exJ sevm) (B (exJ sevm).toNat - dyOut -
          exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xbc0 →
      Region img' 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut) → WordAt img' 0x920 dyOut →
      G = g + 1225 + exStoreCost sevm b (B (exI sevm).toNat + D)
        (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) →
      ∀ bI1 : Devm, Devm.EqModGas bI1 (identityCallNext sevm (exStoreBase sevm b
        (B (exI sevm).toNat + D) (B (exJ sevm).toNat - dyOut -
          exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))) exStoreS1
        (exStoreM1 M sevm dyFee (σ.get adminFeeSlot)) (Bytes.toB256 [10, 64] + Bytes.toB256 [32])
        (Bytes.toB256 [4]) (Bytes.toB256 [10, 160] + Bytes.toB256 [0] + Bytes.toB256 [32])
        (Bytes.toB256 [4])) →
      Devm.EqModGas b' (identityCallNext sevm bI1 exStoreS2
        (exStoreM2 M sevm dyFee (σ.get adminFeeSlot) dyOut) (Bytes.toB256 [10, 160])
        (Bytes.toB256 [32] + exPushLen) (Bytes.toB256 [11, 64]) (Bytes.toB256 [32] + exPushLen)) →
      M' = exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut →
      SFunc.RunEx cert.prog sevm (St b' [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
        Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M' g) t_2b49_c1174 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_296f_c1174 Q := by
  have hrj := hF.rate _ hj
  have hoi := hF.old _ hi
  have hoj := hF.old _ hj
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 10 := ⟨G - 10, by omega⟩
  wrun 2
  xr (rxm_mload (o := 0x940) hR hsz rfl (by decide) (by hr) ·)
  rw [hfee.read]
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVE hfork (by hr) (by unfold exStoreCost at hG; omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hx_g2; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  rw [adminFeeSlot_lit] at hv2; subst hv2
  have hc4 : exStoreCost sevm b (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) =
      sloadCost sevm b (Bytes.toB256 [3]) +
        sstoreCost sevm b2 (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]))
          (B (exI sevm).toNat + D) +
        sstoreCost sevm (afterSstore sevm b2 (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]))
            (B (exI sevm).toNat + D)) (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
          (B (exJ sevm).toNat - dyOut - dyFee * σ.get adminFeeSlot / Bytes.toB256 [2, 84, 11, 228, 0] *
            Bytes.toB256 [13, 224, 182, 179, 167, 100, 0, 0] / exRate (exJ sevm).toNat) := by
    rw [hb2]; rfl
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 477 := ⟨g2 - 477, by omega⟩
  wrun 12
  xr (rx_branch_succ (ex_mulGuard hma) ·)
  -- tree t_298a_c1174
  wrun 12
  xr (rx_branch_succ (by decide) ·)
  -- tree t_29a2_c1174
  wrun 8
  refine rxe_mstoreW (o := 0xa20) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa00 0xa20 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0xa20) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 13
  xr (rx_branch_succ (ex_mulGuard hmap) ·)
  -- tree t_29cd_c1174
  wrun 15
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_29e7_c1174
  wrun 4
  xr (rxm_mloadW (v := exRate (exJ sevm).toNat) (o := 0x140 + 32 * (exJ sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0x40]) hj (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoH hrj) (by hr) ·)
  wrun 3
  xr (rx_branch_succ exRate_ne ·)
  -- tree t_29f7_c1174
  wrun 8
  refine rxe_mstoreW (o := 0xa20) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xa20 32 = 0xa40 by decide] at hsz
  wrun 7
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_2a14_c1174
  wrun 4
  xr (rxm_mloadW (v := B (exI sevm).toNat) (o := 0x1a0 + 32 * (exI sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0xa0]) hi (by decide) (by decide)) ⟨by omega, by decide⟩ ((hoi.write_other (by simp only [B256.length_toBytes]; omega)).write_other (by simp only [B256.length_toBytes]; omega)) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl (by decide) (by hr) ·); try wsimp
  try rw [hF.dx.read]
  wrun 7
  xr (rx_branch_succ (ex_geGuard hbi) ·)
  -- tree t_2a2c_c1174
  wrun 14
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_2a43_c1174
  wrun 3
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xc0 32 = 0xa40 by decide] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sstoreVE hfork hstatic (by omega) (by simp only [gCallStipend]; omega) ?_; intro g4 b4 hb4 hg41 hx_g4; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 231 := ⟨g4 - 231, by omega⟩
  wrun 7
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2a62_c1174
  wrun 4
  xr (rxm_mloadW (v := B (exJ sevm).toNat) (o := 0x1a0 + 32 * (exJ sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0xa0]) hj (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoH hoj) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  try rw [hout.read]
  wrun 5
  xr (rx_branch_succ (ex_geGuard hbj1) ·)
  -- tree t_2a78_c1174
  wrun 9
  xr (rxm_mload (o := 0xa20) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 5
  xr (rx_branch_succ (ex_geGuard hbj2) ·)
  -- tree t_2a90_c1174
  wrun 14
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2aa7_c1174
  wrun 3
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xc0 32 = 0xa40 by decide] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  rw [← hb4] at hc4
  refine rxe_sstoreVE hfork hstatic (by omega) (by simp only [gCallStipend]; omega) ?_; intro g6 b6 hb6 hg61 hx_g6; replace hL := hL.sstoreE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 507 := ⟨g6 - 507, by omega⟩
  wrun 3
  refine rxe_mstoreW (o := 0xa40) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xa40 32 = 0xa60 by decide] at hsz
  wrun 2
  refine rxe_mstoreW (o := 0xa60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa60 0xa60 32 = 0xa80 by decide] at hsz
  wrun 15
  refine rxe_identityL (i := 0xa60) (n := 0x4) (o := 0xac0) (z := 0x4) (ext := 10) (X := 128) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 10 + 64 * idCost 0x4 = 1262 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI1 M hsha hcan1 hMI1 hR hW hsz; rw [show memExtsSize 0xa80 [(0xa60, 0x4), (0xac0, 0x4)] = 0xae0 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [ex_push_sel] at hR
  wrun 3
  xr (rxm_mload (o := 0xa40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 2
  xr (rx_swap2 ·)
  wrun 8
  refine rxe_mstoreW (o := 0xac4) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xae0 0xac4 32 = 0xb00 by decide] at hsz
  wrun 6
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  try rw [hout.read]
  wrun 5
  refine rxe_mstoreW (o := 0xae4) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xb00 0xae4 32 = 0xb20 by decide] at hsz
  wrun 7
  refine rxe_mstoreW (o := 0xaa0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xb20 0xaa0 32 = 0xb20 by decide] at hsz
  wrun 4
  xr (rxm_mload (o := 0xaa0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 9
  refine rxe_identityL (i := 0xaa0) (n := 0x64) (o := 0xb40) (z := 0x64) (ext := 17) (X := 144) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 17 + 64 * idCost 0x64 = 1845 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI M hsha hcan2 hMI2 hR hW hsz; rw [show memExtsSize 0xb20 [(0xaa0, 0x64), (0xb40, 0x64)] = 0xbc0 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [transfer_copy2] at hR
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img3 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut) := by
    rw [hI]; exact Region.write_self _ _ _
  have hout3 : WordAt img3 0x920 dyOut := by rw [hI]; wautoH hout
  have hc : exStoreCost sevm b (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) =
      sloadCost sevm b (Bytes.toB256 [3]) +
        sstoreCost sevm b2 (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]))
          (B (exI sevm).toNat + D) +
        sstoreCost sevm b4 (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
          (B (exJ sevm).toNat - dyOut - dyFee * σ.get adminFeeSlot / Bytes.toB256 [2, 84, 11, 228, 0] *
            Bytes.toB256 [13, 224, 182, 179, 167, 100, 0, 0] / exRate (exJ sevm).toNat) := by
    rw [hb4, hb2]; rfl
  refine k bI M img3 g7 hL hR hW hsz hdata hout3 (by omega) bI1 ?_ ?_ ?_
  · rw [hb6, hb4, hb2] at hcan1; exact hcan1
  · rw [hMI1] at hcan2; exact hcan2
  · rw [hMI2, hMI1]; rfl


/-- `transferFrom`'s call site over `M`: its calldata and the memory's size. -/
structure ExPullWin (sevm : Sevm) (M : Mem) : Prop where
  read : ((exPullI2 M sevm).read 0x600 0x64).1 = transferFromSel ++ sevm.caller.toB256.toBytes ++
    sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes
  size : (exPullI2 M sevm).size = 0x680

/-- `transfer`'s call site over `M`: its calldata and the memory's size. -/
structure ExPushWin (sevm : Sevm) (M : Mem) (dyOut : B256) : Prop where
  read : ((M.write 0xc0 (Bytes.toB256 [0]).toBytes).read 0xb60 0x44).1 =
    transferSel ++ sevm.caller.toB256.toBytes ++ dyOut.toBytes
  size : (M.write 0xc0 (Bytes.toB256 [0]).toBytes).size = 0xbc0

theorem rx_ex_pull_coreF {sevm : Sevm} {b : Devm} {σ : Stor} {G Rf U K Db : Nat} {Q : Outcome → Prop}
    {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256}
    (_hfork : ShanghaiOnwards sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) {s c0 : Nat} (hsz : M.size = s)
    (hs : (s = 0x3c0 ∧ c0 = 31) ∨ (s = 0x460 ∧ c0 = 15)) (hF : ExFrame img B X D C)
    (hp : MutableFloorProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U K 0x600 0x64 0x6c0 debit next)
    (hK : K ≤ Rf) (hK0 : 2000 ≤ K)
    (hDb : ∀ bI1 bI, Devm.EqModGas bI1 (identityCallNext sevm b exPullS1 (exPullM1 M) (Bytes.toB256 [4, 192] +
        Bytes.toB256 [32]) (Bytes.toB256 [4]) (Bytes.toB256 [5, 32] + Bytes.toB256 [0] +
        Bytes.toB256 [32]) (Bytes.toB256 [4])) →
      Devm.EqModGas bI (identityCallNext sevm bI1 exPullS2 (exPullM2 M sevm) (Bytes.toB256 [5, 32])
        (Bytes.toB256 [32] + exPullLen) (Bytes.toB256 [5, 224]) (Bytes.toB256 [32] + exPullLen)) →
      debit bI [] (exPullI2 M sevm) = Db)
    (hG : G = Rf + 575 + c0 + Db) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      ∀ bI1 bI d : Devm,
      Devm.EqModGas bI1 (identityCallNext sevm b exPullS1 (exPullM1 M) (Bytes.toB256 [4, 192] +
        Bytes.toB256 [32]) (Bytes.toB256 [4]) (Bytes.toB256 [5, 32] + Bytes.toB256 [0] +
        Bytes.toB256 [32]) (Bytes.toB256 [4])) →
      Devm.EqModGas bI (identityCallNext sevm bI1 exPullS2 (exPullM2 M sevm) (Bytes.toB256 [5, 32])
        (Bytes.toB256 [32] + exPullLen) (Bytes.toB256 [5, 224]) (Bytes.toB256 [32] + exPullLen)) →
      ExactE debit next bI [] (exPullI2 M sevm) (G - (575 + c0)) d →
      d.gasLeft = g + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d [] d.memory exPullSite) →
      M' = vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32) → ExPullWin sevm M →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_2666_c12 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2517_c11 Q := by
  have hc0 : c0 ≤ 31 := by omega
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ = M := ⟨M, rfl⟩
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 565 + c0 + 10 := ⟨G - 575 - c0, by omega⟩
  wrun 4
  refine rxe_mstoreW (o := 0x4c0) (c := c0) hR hW hsz rfl
    (by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) ?_
  have hs' : memExtSize s 0x4c0 32 = 0x4e0 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  clear hR hW hsz; intro hR hW hsz; rw [hs'] at hsz
  wrun 2
  refine rxe_mstoreW (o := 0x4e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x4e0 0x4e0 32 = 0x500 by decide] at hsz
  wrun 15
  refine rxe_identityL (i := 0x4e0) (n := 0x4) (o := 0x540) (z := 0x4) (ext := 9) (X := 127) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 9 + 64 * idCost 0x4 = 1261 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI1 M hsha hcan1 hMI1 hR hW hsz; rw [show memExtsSize 0x500 [(0x4e0, 0x4), (0x540, 0x4)] = 0x560 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [ex_pull_sel] at hR
  wrun 3
  xr (rxm_mload (o := 0x4c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 11
  refine rxe_mstoreW (o := 0x544) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x560 0x544 32 = 0x580 by decide] at hsz
  wrun 5
  xr (rx_address (by hr) ·)
  wrun 5
  refine rxe_mstoreW (o := 0x564) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x580 0x564 32 = 0x5a0 by decide] at hsz
  wrun 12
  refine rxe_mstoreW (o := 0x584) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x5a0 0x584 32 = 0x5c0 by decide] at hsz
  wrun 7
  refine rxe_mstoreW (o := 0x520) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x5c0 0x520 32 = 0x5c0 by decide] at hsz
  wrun 4
  xr (rxm_mload (o := 0x520) hR hsz rfl (by decide) (by hr) ·); try wsimp
  wrun 9
  refine rxe_identityL (i := 0x520) (n := 0x84) (o := 0x5e0) (z := 0x84) (ext := 19) (X := 149) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 19 + 64 * idCost 0x84 = 2039 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI M hsha hcan2 hMI2 hR hW hsz; rw [show memExtsSize 0x5c0 [(0x520, 0x84), (0x5e0, 0x84)] = 0x680 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [transferFrom_copy] at hR
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img3 0x5e0 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes ++ exPullData sevm) := by
    rw [hI]; exact Region.write_self _ _ _
  have hF3 : ExFrame img3 B X D C := hF.mono fun o v hv ho => by rw [hI]; wauto
  clear hI hF
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_25bc_c11
  wrun 6
  xr (rxm_mload (o := 0x5e0) hR hsz rfl (by decide) (by hr) ·)
  rw [(Region.word hdata.left).read]
  wrun 3
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  rw [hF3.coin.read]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] +
      Bytes.toB256 [32] = (0x64 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [6, 0] = (0x600 : B256) by decide,
    show Bytes.toB256 [6, 192] = (0x6c0 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x600 0x64).1 = transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes := by
    rw [hR.read]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  have hWin : ExPullWin sevm M₀ := by
    have e : M = exPullI2 M₀ sevm := by rw [hMI2, hMI1, hM₀]; rfl
    exact ⟨by rw [← e]; exact hin, by rw [← e]; exact hsz⟩
  have hDbM : debit bI [] M = Db := by
    rw [hMI2, hMI1]; exact hDb bI1 bI hcan1 (by rw [hMI1] at hcan2; exact hcan2)
  obtain ⟨-, d, hrun, hgas, hnext, hpost, hok, hrdlt, hstor, hWd, hidd⟩ :=
    hp.sound bI [] M g1 ⟨hL.w, by omega, by omega, hin, by hr⟩
  have hE : ExactE debit next bI [] M g1 d := ⟨hgas, hnext⟩
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x600 : B256).toNat = 0x600 by decide, show (0x64 : B256).toNat = 0x64 by decide,
    show (0x6c0 : B256).toNat = 0x6c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, ex_pull_tail]
  have hext : (M.extends [(0x600, 0x64), (0x6c0, 0x20)]).size = 0x6e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x6e0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt img3 0x6c0 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail_canonical hLd.id
    hdepth (by decide) ex_pull_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [exPullSite.lh, exPullSite.ll]).toNat + 32 = 0x6c0 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [exPullSite.lh, exPullSite.ll]).toNat = 0x6a0 by decide,
    show (Bytes.toB256 [exPullSite.bh, exPullSite.bl]).toNat = 0x460 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 0x6c0 (d.returnData.take 0x20)) 0x6a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x460 ((Bytes.writeAt (Bytes.writeAt
        img3 0x6c0 (d.returnData.take 0x20)) 0x6a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x6a0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32)).size = 0x6e0 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x6a0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x6e0 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  refine k b' _ _ G2 (hLd.sha hsha) hR6 hW6 hsz6 (hF3.mono fun o v hv ho => by wauto)
    bI1 bI d hcan1 ?_ ?_ hG2 hcanT rfl (hM₀ ▸ hWin)
  · rw [hMI1] at hcan2; exact hcan2
  · rw [hMI2, hMI1] at hE
    rw [show g1 + 565 + c0 + 10 - (575 + c0) = g1 by omega]; exact hE


theorem rx_ex_push_coreF {sevm : Sevm} {b : Devm} {σ : Stor} {G U K Rf R c : Nat} {Q : Outcome → Prop}
    {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {dyOut : B256}
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hj : (exJ sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xbc0)
    (hdata : Region img 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut))
    (hout : WordAt img 0x920 dyOut)
    (hp : MutableFloorProfile sevm W W' (σ.get (coinsBase + exJ sevm)) (transferSel ++
      sevm.caller.toB256.toBytes ++ dyOut.toBytes) RawCallOk U K 0xb60 0x44 0xc00 debit next)
    (hK : K ≤ Rf) (hK0 : 2000 ≤ K)
    (hG : G = Rf + 108 + sloadCost sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36])) +
      debit (afterSload sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) []
        (M.write 0xc0 (Bytes.toB256 [0]).toBytes))
    (hRf : ∀ d, Devm.EqModGas d (next (afterSload sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) []
        (M.write 0xc0 (Bytes.toB256 [0]).toBytes)) → Rf = R + 2232 + c + rawTailCost (min d.returnData.length 32))
    (hc : ∀ d b', Devm.EqModGas d (next (afterSload sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) []
        (M.write 0xc0 (Bytes.toB256 [0]).toBytes)) → Devm.EqModGas b' (rawTailBaseNext sevm d [] d.memory exPushSite) →
      sstoreCost sevm b' (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) = c)
    (hsentry : gCallStipend < R + c) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      D.gasLeft = R →
      (∃ d b' l S' M' G', Devm.EqModGas d (next (afterSload sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) []
          (M.write 0xc0 (Bytes.toB256 [0]).toBytes)) ∧ Devm.EqModGas b' (rawTailBaseNext sevm d [] d.memory exPushSite) ∧
        D = St (afterSstore sevm (b'.addLog l) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])) S' M' G') →
      ExPushWin sevm M dyOut → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
      Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M G) t_2b49_c1174 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 106 := ⟨G - 106, by omega⟩
  wrun 6
  xr (rxm_mload (o := 0xb40) hR hsz rfl (by decide) (by hr) ·)
  rw [(Region.word hdata.left).read]
  wrun 8
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2b69_c1174
  wrun 3
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; generalize hMc : M.write 0xc0 (Bytes.toB256 [0]).toBytes = Mc; intro hR hW hsz; rw [show memExtSize 0xbc0 0xc0 32 = 0xbc0 by decide] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hr) ·)
  refine rxe_sloadVE hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hx_g2; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
      (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [11, 96] = (0xb60 : B256) by decide,
    show Bytes.toB256 [12, 0] = (0xc00 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  subst hv2
  have hin : (Mc.read 0xb60 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++
      dyOut.toBytes := by
    rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  have hWin : ExPushWin sevm M dyOut := by
    constructor
    · rw [hMc]; exact hin
    · rw [hMc]; exact hsz
  have hGM : debit b2 [] Mc = debit (afterSload sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) []
      (M.write 0xc0 (Bytes.toB256 [0]).toBytes) := by rw [hb2, hMc]
  obtain ⟨-, d, hrun, hgas, hnext, hpost, hok, hrdlt, hstor, hWd, hidd⟩ :=
    hp.sound b2 [] Mc g3 ⟨hL.w, by rw [hGM]; omega, by omega, hin, by hrs⟩
  have hnext' : Devm.EqModGas d (next (afterSload sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) []
      (M.write 0xc0 (Bytes.toB256 [0]).toBytes)) := by rw [← hb2, hMc]; exact hnext
  have hRfd := hRf d hnext'
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0xb60 : B256).toNat = 0xb60 by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0xc00 : B256).toNat = 0xc00 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, ex_push_tail]
  have hext : (Mc.extends [(0xb60, 0x44), (0xc00, 0x20)]).size = 0xc20 := by
    show memExtsSize Mc.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0xc20 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img 192 (Bytes.toB256 [0]).toBytes)
      0xc00 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail_canonical hLd.id
    hdepth (by decide) ex_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [exPushSite.lh, exPushSite.ll]).toNat + 32 = 0xc00 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [exPushSite.lh, exPushSite.ll]).toNat = 0xbe0 by decide,
    show (Bytes.toB256 [exPushSite.bh, exPushSite.bl]).toNat = 0x460 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0xbe0 0x460 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 192 (Bytes.toB256 [0]).toBytes)
        0xc00 (d.returnData.take 0x20)) 0xbe0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x460 ((Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt img 192 (Bytes.toB256 [0]).toBytes) 0xc00 (d.returnData.take 0x20)) 0xbe0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0xbe0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0xbe0 0x460 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0xbe0 0x460 (min d.returnData.length 32)).size = 0xc20 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0xbe0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0xc20 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
  have hout6 : WordAt img6 0x920 dyOut := by rw [hI]; wautoH hout
  clear hI hR6
  have hW := hW6
  have hsz := hsz6
  replace hL := hLd.sha hsha
  clear hW6 hsz6 hR5 hW5 hmem
  obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 2232 := ⟨G2 - 2232, by omega⟩
  wrun 4
  refine rxe_mstoreW (o := 0xc40) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xc20 0xc40 32 = 0xc60 by decide] at hsz
  wrun 3
  refine rxe_mstoreW (o := 0xc60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xc60 0xc60 32 = 0xc80 by decide] at hsz
  wrun 3
  refine rxe_mstoreW (o := 0xc80) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xc80 0xc80 32 = 0xca0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·)
  wsimp
  rw [hout6.read]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xca0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xca0 0xca0 32 = 0xcc0 by decide] at hsz
  wrun 4
  xr (rx_log2 (c := 2149) hstatic (by rw [St.extCost_eq hsz]; decide) rfl (read_covered_len hsz (by decide) (by decide)) ·)
  wrun 2
  have hcd := hc d b' hnext' hcanT
  refine rxe_sstoreVE hfork hstatic (by
    show sstoreCost sevm b' (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) ≤ _
    omega) (by omega) ?_; intro g9 b9 hb9 hg91 hx_g9; replace hL := (hL.addLogE _).sstoreE hb9
  have hlog : ∀ (x : Devm) (l : Log), sstoreCost sevm (x.addLog l) (Bytes.toB256 [255, 255, 255])
      (Bytes.toB256 [0]) = sstoreCost sevm x (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) :=
    fun _ _ => rfl
  rw [hlog] at hx_g9
  subst hb9
  exact ⟨_, .last rfl, k _ (hL.st _ _ _) (by simp only [St.gasLeft]; omega) ⟨d, b', _, _, _, _, hnext', hcanT, rfl⟩ hWin⟩

end Blanc.Lift.Curve3Pool
