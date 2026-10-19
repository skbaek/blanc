import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveY

/-!
# `exchange`, forward: `dy`, the fee and the slippage check

`rx_ex_dy` is `xa_ex_dy`'s forward twin (`t_27fc_c1174` → `t_296f_c1174`): `dy = xp[j] - y - 1`
at `0x920`, `dy_fee` at `0x940`, `dy = (dy - dy_fee) * PRECISION / rates[j]`, `dy ≥ min_dy`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The first word of `exchange`'s slippage message. -/
def exErr0 : B256 := Bytes.toB256 [0x45, 0x78, 0x63, 0x68, 0x61, 0x6e, 0x67, 0x65, 0x20, 0x72, 0x65,
  0x73, 0x75, 0x6c, 0x74, 0x65, 0x64, 0x20, 0x69, 0x6e, 0x20, 0x66, 0x65, 0x77, 0x65, 0x72, 0x20,
  0x63, 0x6f, 0x69, 0x6e, 0x73]

/-- The second word of `exchange`'s slippage message. -/
def exErr1 : B256 := Bytes.toB256 [0x20, 0x74, 0x68, 0x61, 0x6e, 0x20, 0x65, 0x78, 0x70, 0x65, 0x63,
  0x74, 0x65, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00]

/-- The literal memory `dy` leaves: `y` at `0x7c0`, `dy`'s three stages at `0x920`/`0x940`, and
the slippage error buffer `0x960 … 0x9e0`. -/
def exDyMem (M : Mem) (xj y fee r : B256) : Mem :=
  M.write 0x7c0 y.toBytes |>.write 0x920 (exDy0 xj y).toBytes |>.write 0x940 (exDyFee xj y fee).toBytes
    |>.write 0x920 (exDyOut xj y fee r).toBytes
    |>.write 0x960 (Bytes.toB256 [0x08, 0xc3, 0x79, 0xa0]).toBytes
    |>.write 0x980 (Bytes.toB256 [0x20]).toBytes |>.write 0x9a0 (Bytes.toB256 [0x2e]).toBytes
    |>.write 0x9c0 exErr0.toBytes |>.write 0x9e0 exErr1.toBytes

/-- **`dy`, forward, exactly**: `rx_ex_dy`, the continuation also receiving the exact charge
(`612` plus the `fee` load), the base, and the literal memory `exDyMem` (the slippage error
buffer is written on the success path too). -/
theorem rx_ex_dy_core {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C y : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ)
    (hj : (exJ sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hF : ExFrame img B X D C) (hy : WordAt img 0x900 y)
    (hy1 : ¬ X (exJ sevm).toNat < y) (hy2 : ¬ X (exJ sevm).toNat - y < Bytes.toB256 [1])
    (hmf : exDy0 (X (exJ sevm).toNat) y * σ.get feeSlot / exDy0 (X (exJ sevm).toNat) y =
      σ.get feeSlot ∨ exDy0 (X (exJ sevm).toNat) y = 0)
    (hsf : ¬ exDy0 (X (exJ sevm).toNat) y < exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot))
    (hmo : (exDy0 (X (exJ sevm).toNat) y - exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot)) *
      exR0 / (exDy0 (X (exJ sevm).toNat) y - exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot)) =
        exR0 ∨
      exDy0 (X (exJ sevm).toNat) y - exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot) = 0)
    (hmin : ¬ exDyOut (X (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) <
      exMinDy sevm)
    (hG : 3000 + R ≤ G)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xa00 → ExFrame img' B X D C →
      WordAt img' 0x920 (exDyOut (X (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat)) →
      WordAt img' 0x940 (exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot)) → R ≤ g → g ≤ G →
      G = g + 612 + sloadCost sevm b (Bytes.toB256 [0x02]) →
      b' = afterSload sevm b (Bytes.toB256 [0x02]) →
      M' = exDyMem M (X (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_296f_c1174 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_27fc_c1174 Q := by
  have hxj := hF.xp _ hj
  have hrj := hF.rate _ hj
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 176 := ⟨G - 176, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hr) ·)
  rw [hy.read]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x7c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x920 0x7c0 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2817_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mloadW (v := X (exJ sevm).toNat) (o := 0x200 + 32 * (exJ sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [2, 0]) hj (by decide) (by decide)) ⟨by omega, by decide⟩ (by wauto) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x7c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hy1) ·)
  -- tree t_282d_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hy2) ·)
  -- tree t_2843_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x920) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x920 0x920 32 = 0x940 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 hx_g2; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  rw [feeSlot_lit] at hv2; subst hv2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 436 := ⟨g2 - 436, by omega⟩
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
  -- tree t_2869_c1174
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
  xr (rx_branch_succ (by decide) ·)
  -- tree t_2881_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x940) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x940 0x940 32 = 0x960 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x940) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hsf) ·)
  -- tree t_28a0_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
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
  xr (rx_branch_succ (ex_mulGuard hmo) ·)
  -- tree t_28c4_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_28de_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mloadW (v := exRate (exJ sevm).toNat) (o := 0x140 + 32 * (exJ sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0x40]) hj (by decide) (by decide)) ⟨by omega, by decide⟩ (by wauto) (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ exRate_ne ·)
  -- tree t_28ee_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x920) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x960 0x920 32 = 0x960 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x960) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x960 0x960 32 = 0x980 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x980) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x980 0x980 32 = 0x9a0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x9a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x9a0 0x9a0 32 = 0x9c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x9c0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x9c0 0x9c0 32 = 0x9e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x9e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x9e0 0x9e0 32 = 0xa00 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hmin) ·)
  refine k b2 _ _ g3 hL hR hW hsz (hF.mono fun o v hv ho => by wauto) (by wauto) (by wauto)
    (by omega) (by omega) (by omega) hb2 rfl

/-- **`dy`, forward.** -/
theorem rx_ex_dy {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C y : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ)
    (hj : (exJ sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hF : ExFrame img B X D C) (hy : WordAt img 0x900 y)
    (hy1 : ¬ X (exJ sevm).toNat < y) (hy2 : ¬ X (exJ sevm).toNat - y < Bytes.toB256 [1])
    (hmf : exDy0 (X (exJ sevm).toNat) y * σ.get feeSlot / exDy0 (X (exJ sevm).toNat) y =
      σ.get feeSlot ∨ exDy0 (X (exJ sevm).toNat) y = 0)
    (hsf : ¬ exDy0 (X (exJ sevm).toNat) y < exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot))
    (hmo : (exDy0 (X (exJ sevm).toNat) y - exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot)) *
      exR0 / (exDy0 (X (exJ sevm).toNat) y - exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot)) =
        exR0 ∨
      exDy0 (X (exJ sevm).toNat) y - exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot) = 0)
    (hmin : ¬ exDyOut (X (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) <
      exMinDy sevm)
    (hG : 3000 + R ≤ G)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xa00 → ExFrame img' B X D C →
      WordAt img' 0x920 (exDyOut (X (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat)) →
      WordAt img' 0x940 (exDyFee (X (exJ sevm).toNat) y (σ.get feeSlot)) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_296f_c1174 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_27fc_c1174 Q :=
  rx_ex_dy_core hfork hL hj hR hW hsz hF hy hy1 hy2 hmf hsf hmo hmin hG
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9

end Blanc.Lift.Curve3Pool
