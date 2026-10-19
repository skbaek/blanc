import Blanc.Lift.Curve3Pool.Callee.AGrow
import Blanc.Lift.Curve3Pool.Walk.LiveLoops
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveY
import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLive
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactKit

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

/-- The base `_calc_withdraw_one_coin`'s `totalSupply()` call runs from: `fee` and the token
slot read after `_A`. -/
def cwSupBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm b (Bytes.toB256 [2])) (Bytes.toB256 [5])

/-- `rx_cw_a2`'s charge before the `totalSupply()` call over a memory of size `n`: `250` for its
instructions, the growing store at `0x1e0`, the `fee` and token slot reads. -/
def cwA2Cost (sevm : Sevm) (b : Devm) (n : Nat) : Nat :=
  250 + (3 + (calculateMemoryGasCost 0x200 - calculateMemoryGasCost n)) +
    sloadCost sevm b (Bytes.toB256 [2]) +
    sloadCost sevm (afterSload sevm b (Bytes.toB256 [2])) (Bytes.toB256 [5])

/-- The `totalSupply()` call's memory: `_A`'s answer and the four frame words stored back, the
adjusted fee, `PRECISION_MUL` and the selector at `0x2a0`. -/
def cwA2Mem (M : Mem) (A x1 x2 x3 x4 : B256) (σ : Stor) : Mem :=
  ((((((((((M.write 0x1e0 A.toBytes).write 0x1a0 x1.toBytes).write 0x180 x2.toBytes).write 0x160
    x3.toBytes).write 0x140 x4.toBytes).write 0x1a0 A.toBytes).write 0x200
    (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]).toBytes).write 0x220
    (Bytes.toB256 [1]).toBytes).write 0x240 (Bytes.toB256 [232, 212, 165, 16, 0]).toBytes).write
    0x260 (Bytes.toB256 [232, 212, 165, 16, 0]).toBytes).write 0x2a0
    (Bytes.toB256 [24, 22, 13, 221]).toBytes

/-- The memory after the `totalSupply()` reply `out` over the call's memory `Ms`: the reply word
at `0x300`, `T` at `0x280`, the save counter at `0x380`. -/
def cwA2Post (Ms : Mem) (out : Bytes) (T : B256) : Mem :=
  ((((Ms.extends [((0x2bc : B256).toNat, (4 : B256).toNat), ((0x300 : B256).toNat, 32)]).write
    0x300 (out.take 32)).write 0x280 T.toBytes).write 0x380 (Bytes.toB256 [1, 64]).toBytes)

/-- **From `_A`'s return to the first frame save, forward, exactly** (core). -/
theorem rx_cw_a2E {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {M : Mem} {img : Bytes}
    {G R U n : Nat} {Q : Outcome → Prop} {W : Devm → Prop} {A x1 x2 x3 x4 T : B256}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = n) (hn : n % 32 = 0)
    (hext : memExtSize n 0x1e0 32 = 0x200)
    (hsup : StaticWordOkAtE sevm W W (σ.get tokenSlot) totalSupplyData T U 0x2bc 4 0x300 E)
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
      ∀ (Gs : Nat) (d : Devm), E (cwSupBase sevm b) S (cwA2Mem M A x1 x2 x3 x4 σ) Gs d →
      G = Gs + cwA2Cost sevm b n → d.gasLeft = g + 77 → b' = d →
      M' = cwA2Post (cwA2Mem M A x1 x2 x3 x4 σ) d.returnData T →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x03, 0x20] :: S) M' g) t_3da4_c36 Q) :
    SFunc.RunEx cert.prog sevm (St b (A :: x1 :: x2 :: x3 :: x4 :: S) M G) t_3cef_c36 Q := by
  have hW'c := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 43 + (3 + (calculateMemoryGasCost 0x200 -
      calculateMemoryGasCost n)) + 4 := ⟨G - 47 - (3 + (calculateMemoryGasCost 0x200 -
      calculateMemoryGasCost n)), by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1e0) (c := 3 + (calculateMemoryGasCost 0x200 - calculateMemoryGasCost n)) hR hW hsz rfl ⟨by rw [hext]; rfl, hn⟩ ?_; clear hR hW hsz; rename' M => M1; intro M hM1 hR hW hsz; rw [hext] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M2; intro M hM2 hR hW hsz; rw [show memExtSize 0x200 0x1a0 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M3; intro M hM3 hR hW hsz; rw [show memExtSize 0x200 0x180 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M4; intro M hM4 hR hW hsz; rw [show memExtSize 0x200 0x160 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M5; intro M hM5 hR hW hsz; rw [show memExtSize 0x200 0x140 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M6; intro M hM6 hR hW hsz; rw [show memExtSize 0x200 0x1a0 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
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
  refine rxe_mstoreL (o := 0x200) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M7; intro M hM7 hR hW hsz; rw [show memExtSize 0x200 0x200 32 = 0x220 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x220) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M8; intro M hM8 hR hW hsz; rw [show memExtSize 0x220 0x220 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x240) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M9; intro M hM9 hR hW hsz; rw [show memExtSize 0x240 0x240 32 = 0x260 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x260) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M10; intro M hM10 hR hW hsz; rw [show memExtSize 0x260 0x260 32 = 0x280 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2a0) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M11; intro M hM11 hR hW hsz; rw [show memExtSize 0x280 0x2a0 32 = 0x2c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g4 b4 v4 hb4 hv4 hg41 hg42 g4x; replace hv4 := hL.val hv4; replace hL := hL.sloadE hb4
  rw [show Bytes.toB256 [5] = tokenSlot by decide] at hv4; subst hv4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 2 := ⟨g4 - 2, by omega⟩
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [2, 188] = (0x2bc : B256) by decide, show Bytes.toB256 [4] = (4 : B256) by decide,
    show Bytes.toB256 [3, 0] = (0x300 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x2bc : B256).toNat (4 : B256).toNat).1 = totalSupplyData := by
    rw [hR.read, show (0x2bc : B256).toNat = 0x2bc by decide, show (4 : B256).toNat = 4 by decide,
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  refine rxe_staticWordAlE (o := 0x300) (s := 0x320) hL hW'c hsup (by omega) (by omega) (by hrs) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2 hMd hE
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
  refine rxe_mstoreL (o := 0x280) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M12; intro M hM12 hR hW hsz; rw [show memExtSize 0x320 0x280 32 = 0x320 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x380) (c := 15) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M13; intro M hM13 hR hW hsz; rw [show memExtSize 0x320 0x380 32 = 0x3a0 by decide] at hsz
  have hMc : M12 = cwA2Mem M1 A x1 x2 x3 x4 σ := by
    rw [hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1]; rfl
  refine k _ M _ g6 hLd hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega) g5 d ?_
    (by unfold cwA2Cost; rw [← hb2]; omega) hg6 rfl ?_
  · rw [hMc, hb4, hb2] at hE
    exact hE
  · rw [hM13, hM12, hMd, hMc, hrd]; rfl


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
    SFunc.RunEx cert.prog sevm (St b (A :: x1 :: x2 :: x3 :: x4 :: S) M G) t_3cef_c36 Q :=
  rx_cw_a2E hfork hL hR hW hsz hn hext hsup.withE hmf hG hGb hroom
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 _ _ _ _ _ _ _ =>
      k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

/-- The `totalSupply()` call's memory in `_calc_withdraw_one_coin`, from its entry memory `M`:
the arguments stored at `0x180`, `0x140`, `0x160`, `_A`'s memory (`aMemNext`) and `rx_cw_a2`'s
stores (`cwA2Mem`). -/
def cwAMem (sevm : Sevm) (b : Devm) (σ : Stor) (M : Mem) (ρ a i : B256) (amp : Nat) : Mem :=
  cwA2Mem (aMemNext sevm b (((M.write 0x180 ρ.toBytes).write 0x140 a.toBytes).write 0x160
    i.toBytes) (Nat.toB256 (15593 + 6)) (Nat.toB256 amp)) (Nat.toB256 amp) (memWord M 0x1a0) ρ i
    a σ

/-- **`_calc_withdraw_one_coin`'s charge up to the `totalSupply()` call**: the prologue (`43`),
the call idiom (`19`), `_A` (`aE` and `aGas`) and `rx_cw_a2`'s charge at `_A`'s base. -/
def cwACost (sevm : Sevm) (b : Devm) : Nat :=
  62 + aE sevm b + aGas sevm b + cwA2Cost sevm (aBase sevm b) (aSz sevm b)

/-- **`_calc_withdraw_one_coin` from its entry to the first frame save, forward, exactly**
(core): the arguments
and return address stored, `_A` (`a_exact_1e0`, answering `Aw` with `Aw.toNat = amp`), then
`rx_cw_a2`. -/
theorem rx_cw_aE {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R U amp : Nat} {Q : Outcome → Prop} {W : Devm → Prop} {ρ a i T : B256}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x1e0)
    (hsup : StaticWordOkAtE sevm W W (σ.get tokenSlot) totalSupplyData T U 0x2bc 4 0x300 E)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : aGas sevm b + 4620 + U + R ≤ G) (hGb : G < 2 ^ 256) (hroom : S.length + 24 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat) (Aw : B256), Aw.toNat = amp →
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x3a0 →
      WordAt img' 0x140 a → WordAt img' 0x160 i → WordAt img' 0x180 ρ →
      WordAt img' 0x1a0 Aw → WordAt img' 0x200 (cwFee (σ.get feeSlot)) →
      WordAt img' 0x220 cwP1 → WordAt img' 0x240 cwPm → WordAt img' 0x260 cwPm →
      WordAt img' 0x280 T → WordAt img' 0x380 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      ∀ (Gs : Nat) (d : Devm), E (cwSupBase sevm (aBase sevm b)) S (cwAMem sevm b σ M ρ a i amp) Gs d →
      G = Gs + cwACost sevm b → d.gasLeft = g + 77 → b' = d →
      M' = cwA2Post (cwAMem sevm b σ M ρ a i amp) d.returnData T →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x03, 0x20] :: S) M' g) t_3da4_c36 Q) :
    SFunc.RunEx cert.prog sevm (St b (ρ :: a :: i :: S) M G) t_3cca_c36 Q := by
  have hR0 := hR
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 43 := ⟨G - 43, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Ma1; intro M hMa1 hR hW hsz; rw [show memExtSize 0x1e0 0x180 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Ma2; intro M hMa2 hR hW hsz; rw [show memExtSize 0x1e0 0x140 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Ma3; intro M hMa3 hR hW hsz; rw [show memExtSize 0x1e0 0x160 32 = 0x1e0 by decide] at hsz
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
  obtain ⟨w, ⟨M', hrun, ⟨-, hW', hsz'⟩, hMA⟩, hw⟩ := a_exact_1e0L (G := g1)
    (ret := Nat.toB256 (0x3ce9 + 6)) (S := _ :: _ :: _ :: _ :: S) hfork ha' hA hW hsz
    (by simp only [List.length_cons]; omega)
  refine rxe_pcCall cw_prog_27 (by decide) (by simp only [List.length_cons]; omega) hrun ?_
  refine rx_cw_a2E (R := R) (U := U) hfork hL.aBaseE (Mem.reads_data M') hW' hsz' (aSz_mod sevm b) (aSz_ext sevm b)
    hsup hmf (by have := aE_store sevm b; omega) (by omega) (by omega) ?_
  intro b' M'' img' g hL' hR' hW'' hsz'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hg1' hg2' Gs d hE hGs hd hb
    hM''
  have hw' : w = Nat.toB256 amp := by rw [← hw, toB256_toNat]
  have hx : Bytes.toB256 (List.sliceD img 416 32 0) = memWord Ma1 0x1a0 := by
    unfold memWord; rw [hR0.read]
  rw [hMA, hw', hx, hMa3, hMa2, hMa1] at hE hM''
  exact k b' M'' img' g w hw hL' hR' hW'' hsz'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hg1' (by omega)
    Gs d hE (by unfold cwACost; omega) hd hb hM''


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
    SFunc.RunEx cert.prog sevm (St b (ρ :: a :: i :: S) M G) t_3cca_c36 Q :=
  rx_cw_aE hfork hL ha hA hR hW hsz hsup.withE hmf hG hGb hroom
    fun b' M' img' g Aw hAw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 _ _ _ _ _ _ _ =>
      k b' M' img' g Aw hAw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

end Blanc.Lift.Curve3Pool
