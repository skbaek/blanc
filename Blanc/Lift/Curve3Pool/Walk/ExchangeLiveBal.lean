import Blanc.Lift.Curve3Pool.Walk.ExchangeLivePull

/-!
# `exchange`, forward: the fee coin's two `balanceOf(self)` reads

For `i == FEE_INDEX` the pull is bracketed by two `balanceOf(self)` `STATICCALL`s, each answered by
`CoinBalOkAt`: `rx_ex_bal1` (`t_24d8_c0` → the pull `t_2517_c11`) parks the first answer at
`0x380`; `rx_ex_bal2` (`t_2672_c12` → `x`'s tree `t_26c9_c13`) the checked difference.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A `balanceOf(self)` payload staged at `o`: the selector word, then the pool's address. -/
def exBalIn (M : Mem) (sevm : Sevm) (o : Nat) : Mem :=
  (M.write o (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes).write (o + 0x20)
    sevm.currentTarget.toB256.toBytes

/-- **`rx_ex_bal1`, exactly**: over the relation-carrying premise `StaticWordOkAtE`, the
continuation also receiving `E` at the call's literal input, the exact fixed charge around the
call, and the literal post memory. -/
theorem rx_ex_bal1_core {sevm : Sevm} {b : Devm} {σ : Stor} {G R U : Nat} {Q : Outcome → Prop} {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C B1 : B256}
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0)
    (hF : ExFrame img B X D C) (hbal : StaticWordOkAtE sevm W W C (balanceOfData sevm.currentTarget) B1 U 0x3dc 0x24 0x440 E)
    (hG : 1000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x460 → ExFrame img' B X B1 C → R ≤ g → g ≤ G →
      E b [] (exBalIn M sevm 0x3c0) (G - 44) b' → b'.gasLeft = g + 53 →
      M' = (((exBalIn M sevm 0x3c0).extends [(0x3dc, 0x24), (0x440, 0x20)]).write 0x440
        (b'.returnData.take 0x20)).write 0x380 B1.toBytes →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_2517_c11 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_24d8_c0 Q := by
  have hW'c := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 44 := ⟨G - 44, by omega⟩
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x3c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3c0 0x3c0 32 = 0x3e0 by decide] at hsz
  xr (rx_address (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x3e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3e0 0x3e0 32 = 0x400 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hr) ·)
  wsimp
  rw [hF.coin.read]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [3, 0xdc] = (0x3dc : B256) by decide, show Bytes.toB256 [0x24] = (0x24 : B256) by decide,
    show Bytes.toB256 [4, 0x40] = (0x440 : B256) by decide, show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  refine rxe_staticWordE (o := 0x440) (s := 0x460) hL hW'c hbal (by omega) (by omega) (by hr)
    (by rw [hR.read]; exact bal_input _ _ 0x3c0) hR hW rfl
    (by show memExtsSize _ _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA hrd hg1 hg2 hM' hE
  clear hR hW hsz
  have hR := hR'; have hW := hW'; have hsz := hsz'; clear hR' hW' hsz' 
  obtain ⟨g2, hg2'⟩ : ∃ g, d.gasLeft = g + 53 := ⟨d.gasLeft - 53, by omega⟩
  rw [hg2']
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_24fe_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_returndatasize (by hr) ·)
  xr (rx_gt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  -- tree t_250b_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x440) hR hsz rfl (by decide) (by hr) ·)
  rw [ex_ans_read _ _ _ hlen, hA]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x380) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x460 0x380 32 = 0x460 by decide] at hsz
  refine k d _ _ g2 hLd hR hW hsz ⟨fun k hk => by wautoH (hF.rate k hk),
    fun k hk => by wautoH (hF.old k hk), fun k hk => by wautoH (hF.xp k hk),
    WordAt.write_self _ _ _, by wautoH hF.coin⟩ (by omega) (by omega)
    (by rw [Nat.add_sub_cancel]; exact hE) hg2' (by rw [hM', hrd]; rfl)

/-- **The first `balanceOf(self)`, forward.** -/
theorem rx_ex_bal1 {sevm : Sevm} {b : Devm} {σ : Stor} {G R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C B1 : B256}
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0)
    (hF : ExFrame img B X D C) (hbal : CoinBalOkAt sevm W W C B1 U 0x3dc 0x440)
    (hG : 1000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x460 → ExFrame img' B X B1 C → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_2517_c11 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_24d8_c0 Q :=
  rx_ex_bal1_core hL hR hW hsz hF hbal.withE hG hGb
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7

/-- **`rx_ex_bal2`, exactly**: over the relation-carrying premise `StaticWordOkAtE`, the
continuation also receiving `E` at the call's literal input, the exact fixed charge around the
call, and the literal post memory. -/
theorem rx_ex_bal2_core {sevm : Sevm} {b : Devm} {σ : Stor} {G R U : Nat} {Q : Outcome → Prop} {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {C B1 B2 : B256}
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x6e0)
    (hF : ExFrame img B X B1 C) (hbal : StaticWordOkAtE sevm W W C (balanceOfData sevm.currentTarget) B2 U 0x71c 0x24 0x780 E)
    (hsub : ¬ B2 < B1) (hG : 1000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x7a0 → ExFrame img' B X (B2 - B1) C →
      R ≤ g → g ≤ G → E b [] (exBalIn M sevm 0x700) (G - 47) b' → b'.gasLeft = g + 104 →
      M' = (((exBalIn M sevm 0x700).extends [(0x71c, 0x24), (0x780, 0x20)]).write 0x780
        (b'.returnData.take 0x20)).write 0x380 (B2 - B1).toBytes →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2672_c12 Q := by
  have hW'c := hL.wc
  have hD := hF.dx
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 47 := ⟨G - 47, by omega⟩
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x700) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x6e0 0x700 32 = 0x720 by decide] at hsz
  xr (rx_address (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x720) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x720 0x720 32 = 0x740 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hr) ·)
  wsimp
  rw [hF.coin.read]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [7, 0x1c] = (0x71c : B256) by decide, show Bytes.toB256 [0x24] = (0x24 : B256) by decide,
    show Bytes.toB256 [7, 0x80] = (0x780 : B256) by decide, show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  refine rxe_staticWordE (o := 0x780) (s := 0x7a0) hL hW'c hbal (by omega) (by omega) (by hr)
    (by rw [hR.read]; exact bal_input _ _ 0x700) hR hW rfl
    (by show memExtsSize _ _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA hrd hg1 hg2 hM' hE
  clear hR hW hsz
  have hR := hR'; have hW := hW'; have hsz := hsz'; clear hR' hW' hsz' 
  obtain ⟨g2, hg2'⟩ : ∃ g, d.gasLeft = g + 104 := ⟨d.gasLeft - 104, by omega⟩
  rw [hg2']
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_2698_c12
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_returndatasize (by hr) ·)
  xr (rx_gt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  -- tree t_26a5_c12
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x780) hR hsz rfl (by decide) (by hr) ·)
  rw [ex_ans_read _ _ _ hlen, hA]
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl (by decide) (by hr) ·); try wsimp
  rw [hD.read]
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hsub) ·)
  -- tree t_26bd_c12
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x380) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x7a0 0x380 32 = 0x7a0 by decide] at hsz
  refine k d _ _ g2 hLd hR hW hsz ⟨fun k hk => by wautoH (hF.rate k hk),
    fun k hk => by wautoH (hF.old k hk), fun k hk => by wautoH (hF.xp k hk),
    WordAt.write_self _ _ _, by wautoH hF.coin⟩ (by omega) (by omega)
    (by rw [Nat.add_sub_cancel]; exact hE) hg2' (by rw [hM', hrd]; rfl)

/-- **The second `balanceOf(self)` and the credited amount, forward.** -/
theorem rx_ex_bal2 {sevm : Sevm} {b : Devm} {σ : Stor} {G R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {C B1 B2 : B256}
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x6e0)
    (hF : ExFrame img B X B1 C) (hbal : CoinBalOkAt sevm W W C B2 U 0x71c 0x780)
    (hsub : ¬ B2 < B1) (hG : 1000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x7a0 → ExFrame img' B X (B2 - B1) C →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' [] M' g) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2672_c12 Q :=
  rx_ex_bal2_core hL hR hW hsz hF hbal.withE hsub hG hGb
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7

end Blanc.Lift.Curve3Pool
