import Blanc.Lift.Curve3Pool.Walk.ExchangeLivePull

/-!
# `exchange`, forward: `x`

`rx_ex_x` is `xa_ex_x`'s forward twin (`t_26c9_c13` → the frame save `t_2754_c13`):
`x = xp[i] + dx_w_fee * rates[i] / PRECISION` (checked) at `0x7a0`, the save counter at `0x7e0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`x`, forward, exactly**: `rx_ex_x`, the continuation also receiving its exact charge
`279 + c0` and the literal memory (`x` at `0x7a0`, the save counter at `0x7e0`). -/
theorem rx_ex_x_core {sevm : Sevm} {b : Devm} {G R : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C : B256} {s c0 : Nat}
    (hi : (exI sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x6e0 ∧ c0 = 26) ∨ (s = 0x7a0 ∧ c0 = 6)) (hF : ExFrame img B X D C)
    (hmx : D * exRate (exI sevm).toNat / D = exRate (exI sevm).toNat ∨ D = 0)
    (hax : ¬ X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0 < X (exI sevm).toNat)
    (hG : 400 + R ≤ G)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x800 →
      ExFrame img' B X D C →
      WordAt img' 0x7a0 (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0) →
      WordAt img' 0x7e0 (Bytes.toB256 [1, 0x40]) → R ≤ g → g ≤ G →
      G = g + 279 + c0 →
      M' = (M.write 0x7a0 (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toBytes).write
        0x7e0 (Bytes.toB256 [1, 0x40]).toBytes →
      SFunc.RunEx cert.prog sevm (St b [] M' g) t_2754_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_26c9_c13 Q := by
  have hs32 : s % 32 = 0 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hs0 : 0x6e0 ≤ s := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hc0 : c0 ≤ 26 := by omega
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 16 + c0 + 263 := ⟨G - 279 - c0, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_26dc_c13
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mload (o := 0x200 + 32 * (exI sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [2, 0]) hi (by decide) (by decide)) ⟨by omega, hs32⟩ (by hr) ·)
  rw [(hF.xp _ hi).read]
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [hF.dx.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_26f8_c13
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mload (o := 0x140 + 32 * (exI sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0x40]) hi (by decide) (by decide)) ⟨by omega, hs32⟩ (by hr) ·)
  rw [(hF.rate _ hi).read]
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
  xr (rx_branch_succ (ex_mulGuard hmx) ·)
  -- tree t_2711_c13
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
  -- tree t_272c_c13
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hax) ·)
  -- tree t_2741_c13
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x7a0) (c := c0) hR hW hsz rfl (by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) ?_
  have hs' : memExtSize s 0x7a0 32 = 0x7c0 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  clear hR hW hsz; intro hR hW hsz; rw [hs'] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x7e0) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x7c0 0x7e0 32 = 0x800 by decide] at hsz
  -- STOP at t_2754_c13
  refine k _ _ g1 hR hW (by rw [hsz]) (hF.mono fun o v hv ho => by wauto) (by wauto) (by wauto)
    (by omega) (by omega) (by omega) rfl

/-- **`x`, forward.** -/
theorem rx_ex_x {sevm : Sevm} {b : Devm} {G R : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C : B256} {s c0 : Nat}
    (hi : (exI sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x6e0 ∧ c0 = 26) ∨ (s = 0x7a0 ∧ c0 = 6)) (hF : ExFrame img B X D C)
    (hmx : D * exRate (exI sevm).toNat / D = exRate (exI sevm).toNat ∨ D = 0)
    (hax : ¬ X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0 < X (exI sevm).toNat)
    (hG : 400 + R ≤ G)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x800 →
      ExFrame img' B X D C →
      WordAt img' 0x7a0 (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0) →
      WordAt img' 0x7e0 (Bytes.toB256 [1, 0x40]) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b [] M' g) t_2754_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_26c9_c13 Q :=
  rx_ex_x_core hi hR hW hsz hs hF hmx hax hG
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7 h8

end Blanc.Lift.Curve3Pool
