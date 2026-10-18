import Blanc.Lift.Curve3Pool.Callee.AGrow
import Blanc.Lift.Curve3Pool.Walk.LiveLoops
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveY
import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec

/-!
# `_calc_withdraw_one_coin`, forward: the prologue, `_A`, the fee and the supply

`rx_cw_a2` (`t_3cef_c36` → the first frame save `t_3da4_c36`): `_A`'s answer and the frame
words stored back, the adjusted fee `fee · 3 / 8` (checked), `PRECISION_MUL`, the token read and
its `totalSupply()` (`SupplyOkAt`, window `0x2bc`/`0x300`) stored at `0x280`, and the save
counter set. `rx_cw_a` adds the prologue and `_A` (`a_exact_1e0`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The adjusted fee word. -/
abbrev cwFee (f : B256) : B256 := f * Bytes.toB256 [0x03] / Bytes.toB256 [0x08]

theorem cw_prog_27 : cert.prog[27]? = some t_00a9_c27 := prog_27

/-- **From `_A`'s return to the first frame save, forward.** -/
theorem rx_cw_a2 {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {M : Mem} {img : Bytes}
    {G R U n : Nat} {Q : Outcome → Prop} {W : Devm → Prop} {A x1 x2 x3 x4 T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = n) (hn : n % 32 = 0)
    (hext : memExtSize n 0x1e0 32 = 0x200)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x2bc 0x300)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : (3 + (calculateMemoryGasCost 0x200 - calculateMemoryGasCost n)) + 4550 + U + R ≤ G)
    (hGb : G < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x3a0 →
      WordAt img' 0x140 x4 → WordAt img' 0x160 x3 → WordAt img' 0x180 x2 →
      WordAt img' 0x1a0 A → WordAt img' 0x200 (cwFee (σ.get feeSlot)) →
      WordAt img' 0x220 cwP1 → WordAt img' 0x240 cwPm → WordAt img' 0x260 cwPm →
      WordAt img' 0x280 T → WordAt img' 0x380 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x03, 0x20] :: S) M' g) t_3da4_c36 Q) :
    SFunc.RunEx cert.prog sevm (St b (A :: x1 :: x2 :: x3 :: x4 :: S) M G) t_3cef_c36 Q := by
  have hW'c := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 43 + (3 + (calculateMemoryGasCost 0x200 -
      calculateMemoryGasCost n)) + 4 := ⟨G - 47 - (3 + (calculateMemoryGasCost 0x200 -
      calculateMemoryGasCost n)), by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x1e0) (c := 3 + (calculateMemoryGasCost 0x200 - calculateMemoryGasCost n)) hR hW hsz rfl ⟨by rw [hext]; rfl, hn⟩ ?_; clear hR hW hsz M; intro M hR hW hsz; rw [hext] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x1a0 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x180 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x160 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x140 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x1a0 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadV hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  rw [show Bytes.toB256 [2] = feeSlot by decide] at hv2; subst hv2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 205 := ⟨g2 - 205, by omega⟩
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_mulGuard hmf) ·)
  -- tree t_3d24_c36
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_3d38_c36
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x200) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x200 32 = 0x220 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstore (o := 0x220) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x220 0x220 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x240) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x240 32 = 0x260 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x260) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x260 0x260 32 = 0x280 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x2a0) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x2a0 32 = 0x2c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadV hfork (by hr) (by omega) ?_; intro g4 b4 v4 hb4 hv4 hg41 hg42; replace hv4 := hL.val hv4; replace hL := hL.sloadE hb4
  rw [show Bytes.toB256 [5] = tokenSlot by decide] at hv4; subst hv4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 2 := ⟨g4 - 2, by omega⟩
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [2, 188] = (0x2bc : B256) by decide, show Bytes.toB256 [4] = (4 : B256) by decide,
    show Bytes.toB256 [3, 0] = (0x300 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x2bc : B256).toNat (4 : B256).toNat).1 = totalSupplyData := by
    rw [hR.read, show (0x2bc : B256).toNat = 0x2bc by decide, show (4 : B256).toNat = 4 by decide,
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  refine rxe_staticWord (o := 0x300) (s := 0x320) hL hW'c hsup (by omega) (by omega) (by hrs) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2
  clear hR hW hsz hin
  have hR := hR'; have hW := hW'; have hsz := hsz'; clear hR' hW' hsz'
  obtain ⟨g6, hg6⟩ : ∃ g, d.gasLeft = g + 77 := ⟨d.gasLeft - 77, by omega⟩
  rw [hg6]
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_3d81_c36
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_returndatasize (by hr) ·)
  xr (rx_gt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  -- tree t_3d8e_c36
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x300) hR hsz rfl (by decide) (by hr) ·)
  rw [ex_ans_read _ _ _ hlen, hA']
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x280) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x320 0x280 32 = 0x320 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x380) (c := 15) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x320 0x380 32 = 0x3a0 by decide] at hsz
  exact k _ M _ g6 hLd hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)

/-- **`_calc_withdraw_one_coin` from its entry to the first frame save, forward**: the arguments
and return address stored, `_A` (`a_exact_1e0`, answering `Aw` with `Aw.toNat = amp`), then
`rx_cw_a2`. -/
theorem rx_cw_a {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R U amp : Nat} {Q : Outcome → Prop} {W : Devm → Prop} {ρ a i T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x1e0)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x2bc 0x300)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : aGas sevm b + 4620 + U + R ≤ G) (hGb : G < 2 ^ 256) (hroom : S.length + 24 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat) (Aw : B256), Aw.toNat = amp →
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x3a0 →
      WordAt img' 0x140 a → WordAt img' 0x160 i → WordAt img' 0x180 ρ →
      WordAt img' 0x1a0 Aw → WordAt img' 0x200 (cwFee (σ.get feeSlot)) →
      WordAt img' 0x220 cwP1 → WordAt img' 0x240 cwPm → WordAt img' 0x260 cwPm →
      WordAt img' 0x280 T → WordAt img' 0x380 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x03, 0x20] :: S) M' g) t_3da4_c36 Q) :
    SFunc.RunEx cert.prog sevm (St b (ρ :: a :: i :: S) M G) t_3cca_c36 Q := by
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 43 := ⟨G - 43, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1e0 0x180 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1e0 0x140 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1e0 0x160 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x180) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  have ha' : Abstracts (b.getStor sevm.currentTarget) s := ha.of_lock fun x _ => hL.stor x
  obtain ⟨g1, hg1⟩ : ∃ g, g0 = g + aE sevm b + aGas sevm b + 19 :=
    ⟨g0 - aE sevm b - aGas sevm b - 19, by have := aE_le sevm b; omega⟩
  rw [hg1]
  obtain ⟨w, ⟨M', hrun, -, hW', hsz'⟩, hw⟩ := a_exact_1e0 (G := g1)
    (ret := Nat.toB256 (0x3ce9 + 6)) (S := _ :: _ :: _ :: _ :: S) hfork ha' hA hW hsz
    (by simp only [List.length_cons]; omega)
  refine rxe_pcCall cw_prog_27 (by decide) (by simp only [List.length_cons]; omega) hrun ?_
  refine rx_cw_a2 (R := R) (U := U) hfork hL.aBaseE (Mem.reads_data M') hW' hsz' (aSz_mod sevm b) (aSz_ext sevm b)
    hsup hmf (by have := aE_store sevm b; omega) (by omega) (by omega) ?_
  intro b' M'' img' g hL' hR' hW'' hsz'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hg1' hg2'
  exact k b' M'' img' g w hw hL' hR' hW'' hsz'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hg1' (by omega)

end Blanc.Lift.Curve3Pool
