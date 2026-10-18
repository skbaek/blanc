import Blanc.Lift.Curve3Pool.Walk.AlLiveD1
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop

/-!
# `add_liquidity`, forward: the fee loop

The loop of lines 325–334 over the counter at `0xa40`, the same body as
`remove_liquidity_imbalance`'s (its checks are `RliFeeIter`). The path skeletons `alFeeHd`
(`0x1409` → the `ideal > new` test), `alFeeZ` / `alFeeS` (the two `difference` arms) and
`alFeeTl` (`0x14f3` → the loop test) take the off-path arms as parameters; every context's tree
is an `rfl` instance. `rx_al_feeArm` runs the head and either arm, `rx_al_feeTl` the rest of an
iteration (`fees[i]` at `0x140 + 32 i`, `balances[i]` stored, `new_balances[i] -= fees[i]` at
`0x460 + 32 i`, the counter bumped).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alFeeHd (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) (a4 : SFunc) (a5 : SFunc) (a6 : SFunc) : SFunc :=
  (.dest (.next (.push [0x09, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x03, 0x00] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x14, 0x21] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg .eq) (.next (.reg .or) (.next (.push [0x14, 0x3a] (by decide)) (.branch a2 (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x02, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x14, 0x50] (by decide)) (.branch a3 (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x0a, 0x60] (by decide)) (.next (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.push [0x0a, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x04, 0x60] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x14, 0x74] (by decide)) (.branch a4 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x0a, 0x60] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next (.reg .iszero) (.next (.push [0x14, 0xbd] (by decide)) (.branch a5 a6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem t_1409_c1273_eq : t_1409_c1273 = alFeeHd .undefined t_1436_c1273 t_144c_c1273 .undefined t_1484_c1273 t_14bd_c1273 := rfl
theorem t_1409_c43_eq : t_1409_c43 = alFeeHd .undefined t_1436_c43 t_144c_c43 .undefined t_1484_c43 t_14bd_c43 := rfl
theorem t_1409_c69_eq : t_1409_c69 = alFeeHd .undefined t_1436_c69 t_144c_c69 .undefined t_1484_c69 t_14bd_c69 := rfl

def alFeeZ (a1 : SFunc) (a2 : SFunc) (a3 : Nat) : SFunc :=
  (.next (.push [0x0a, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x04, 0x60] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x14, 0x9b] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x14, 0xad] (by decide)) (.branch a2 (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x0a, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x14, 0xf3] (by decide)) (.jump a3)))))))))))))))))))))))))))))))))

theorem t_1484_c1273_eq : t_1484_c1273 = alFeeZ .undefined t_14a9_c1273 7 := rfl
theorem t_1484_c43_eq : t_1484_c43 = alFeeZ .undefined t_14a9_c43 68 := rfl
theorem t_1484_c69_eq : t_1484_c69 = alFeeZ .undefined t_14a9_c69 93 := rfl

def alFeeS (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) : SFunc :=
  (.dest (.next (.push [0x04, 0x60] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x14, 0xd1] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x0a, 0x60] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x14, 0xe7] (by decide)) (.branch a2 (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x0a, 0x80] (by decide)) (.next (.reg .mstore) a3))))))))))))))))))))))))))))))))

theorem t_14bd_c1273_eq : t_14bd_c1273 = alFeeS .undefined t_14e3_c1273 t_14f3_c7 := rfl
theorem t_14bd_c43_eq : t_14bd_c43 = alFeeS .undefined t_14e3_c43 t_14f3_c43 := rfl
theorem t_14bd_c69_eq : t_14bd_c69 = alFeeS .undefined t_14e3_c69 t_14f3_c69 := rfl

def alFeeTl (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) (a4 : SFunc) (a5 : SFunc) (a6 : SFunc) (a7 : SFunc) (a8 : SFunc) (a9 : SFunc) (a10 : SFunc) (a11 : SFunc) (a12 : SFunc) (a13 : SFunc) : SFunc :=
  (.dest (.next (.push [0x01, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x0a, 0x80] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg .eq) (.next (.reg .or) (.next (.push [0x15, 0x0f] (by decide)) (.branch a1 (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x15, 0x27] (by decide)) (.branch a2 (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x01, 0x40] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x15, 0x41] (by decide)) (.branch a3 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mstore) (.next (.push [0x04, 0x60] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x15, 0x5a] (by decide)) (.branch a4 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x01, 0x40] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x15, 0x73] (by decide)) (.branch a5 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x01, 0xc0] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg .eq) (.next (.reg .or) (.next (.push [0x15, 0x90] (by decide)) (.branch a6 (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x15, 0xa8] (by decide)) (.branch a7 (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x15, 0xbb] (by decide)) (.branch a8 (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x15, 0xd3] (by decide)) (.branch a9 (.dest (.next (.push [0x01] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.reg .add) (.next (.reg .sstore) (.next (.push [0x04, 0x60] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x15, 0xf3] (by decide)) (.branch a10 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x01, 0x40] (by decide)) (.next (.push [0x0a, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x16, 0x0d] (by decide)) (.branch a11 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x16, 0x1f] (by decide)) (.branch a12 (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.reg .pop) (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x14, 0x09] (by decide)) a13))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem t_14f3_c7_eq : t_14f3_c7 = alFeeTl t_150b_c7 .undefined .undefined .undefined .undefined t_158c_c7 .undefined t_15b7_c7 .undefined .undefined .undefined t_161b_c7 ((.branchTo .undefined 43)) := rfl
theorem t_14f3_c43_eq : t_14f3_c43 = alFeeTl t_150b_c43 .undefined .undefined .undefined .undefined t_158c_c43 .undefined t_15b7_c43 .undefined .undefined .undefined t_161b_c43 ((.branchTo .undefined 69)) := rfl
theorem t_14f3_c68_eq : t_14f3_c68 = alFeeTl t_150b_c68 .undefined .undefined .undefined .undefined t_158c_c68 .undefined t_15b7_c68 .undefined .undefined .undefined t_161b_c68 ((.branchTo .undefined 69)) := rfl
theorem t_14f3_c69_eq : t_14f3_c69 = alFeeTl t_150b_c69 .undefined .undefined .undefined .undefined t_158c_c69 .undefined t_15b7_c69 .undefined .undefined .undefined t_161b_c69 ((.branch t_163a_c69 .undefined)) := rfl
theorem t_14f3_c93_eq : t_14f3_c93 = alFeeTl t_150b_c93 .undefined .undefined .undefined .undefined t_158c_c93 .undefined t_15b7_c93 .undefined .undefined .undefined t_161b_c93 ((.branch t_163a_c93 .undefined)) := rfl

section Fee

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R i : Nat}
  {Q : Outcome → Prop}

/-- **A fee iteration's head and `difference` arm, forward**: `ideal = D1 * B / D0` at `0xa60`
and the difference at `0xa80`, on to the tail `tS` (`ideal ≤ new`) or entry `k`'s `tZ`
(`ideal > new`). Memory `0xa60` (iteration `0`, grown to `0xaa0`) or `0xaa0`. -/
theorem rx_al_feeArm {s c1 c2 k : Nat} {D0 D1 B N : B256} {a1 a2 a3 a4 z1 z2 s1 s2 tS tZ : SFunc}
    (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0xa60 ∧ c1 = 6 ∧ c2 = 7) ∨ (s = 0xaa0 ∧ c1 = 3 ∧ c2 = 3))
    (hctr : WordAt img 0xa40 (Nat.toB256 i)) (hD1 : WordAt img 0x900 D1)
    (hD0w : WordAt img 0x2e0 D0) (hB : WordAt img (0x300 + 32 * i) B)
    (hN : WordAt img (0x460 + 32 * i) N) (hm1 : D1.Nofm B) (hD0 : D0 ≠ 0)
    (hk : cert.prog[k]? = some tZ) (hG : R + 700 ≤ G) (hroom : S.length + 20 < 1024)
    (kk : ∀ (M' : Mem) (img' : Bytes) (g : Nat) (dif : B256) (t : SFunc), Mem.Reads M' img' →
      Mem.Wf M' → M'.size = 0xaa0 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0xa60 ∨ 0xaa0 ≤ o → WordAt img' o w) →
      WordAt img' 0xa80 dif → RliDif (D1 * B / D0) N dif → (t = tS ∨ t = tZ) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M' g) t Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M G)
      (alFeeHd a1 a2 a3 a4 (alFeeZ z1 z2 k) (alFeeS s1 s2 tS)) Q := by
  have hsl : 0xa60 ≤ s ∧ s % 32 = 0 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hc12 : c1 + c2 ≤ 13 := by omega
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 400 + c2 + 6 + c1 + 169 := ⟨G - 575 - c1 - c2, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x900) (v := D1) hR hsz rfl ⟨by omega, hsl.2⟩ (by wautoH hD1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hsl.2⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x300 + 32 * i) (v := B) hR hsz (al_off hi 0x300 (by decide) _ (by decide)) ⟨by omega, hsl.2⟩ (by wautoH hB) (by hrs) ·)
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
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm1) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := D0) hR hsz rfl ⟨by omega, hsl.2⟩ (by wautoH hD0w) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ hD0 ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xa60) (c := c1) hR hW hsz rfl
    (by rcases hs with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> decide) ?_
  clear hR hW hsz M; intro M hR hW hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xa80) (c := c2) hR hW hsz rfl
    (by rcases hs with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ <;> decide) ?_
  have hs' : memExtSize (memExtSize s 0xa60 32) 0xa80 32 = 0xaa0 := by
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  clear hR hW hsz M; intro M hR hW hsz; rw [hs'] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x460 + 32 * i) (v := N) hR hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by wautoH hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0xa60) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  have hP : ∀ o w, WordAt img o w → o + 32 ≤ 0xa60 ∨ 0xaa0 ≤ o →
      WordAt (Bytes.writeAt (Bytes.writeAt img 0xa60 (D1 * B / D0).toBytes) 0xa80
        (Bytes.toB256 [0]).toBytes) o w := fun o w hw ho => by
    refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
    refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
    exact hw
  by_cases hlt : N < D1 * B / D0
  · -- `ideal > new`
    xr (rx_branch_zero' (gtCheck_iszero_of_lt (B256.lt_iff_toNat_lt_toNat.mp hlt)) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0xa60) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rxm_mloadW (o := 0x460 + 32 * i) (v := N) hR hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by wautoH hN) (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_geGuard (fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.lt_asymm (B256.lt_iff_toNat_lt_toNat.mp hlt)))) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_sub (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreK (o := 0xa80) hR hW hsz rfl ⟨by decide, by decide⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_jump (g := tZ) hk ·)
    exact kk M _ _ _ tZ hR hW hsz (fun o w hw ho => by
        refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
        exact hP o w hw ho) (by wauto) (.inl ⟨hlt, rfl⟩) (.inr rfl) (by omega) (by omega)
  · -- `ideal ≤ new`
    xr (rx_branch_succ (gtCheck_iszero_of_not_lt (fun h => hlt (B256.lt_iff_toNat_lt_toNat.mpr h))) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rxm_mloadW (o := 0x460 + 32 * i) (v := N) hR hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by wautoH hN) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0xa60) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_geGuard hlt) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_sub (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreK (o := 0xa80) hR hW hsz rfl ⟨by decide, by decide⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    exact kk M _ _ _ tS hR hW hsz (fun o w hw ho => by
        refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
        exact hP o w hw ho) (by wauto) (.inr ⟨hlt, rfl⟩) (.inl rfl) (by omega) (by omega)

/-- **A fee iteration's tail, forward** (`0x14f3` → the loop test): `fees[i] = F * dif / FEE`,
`balances[i] = N - fees[i] * AF / FEE` stored, `new_balances[i] = N - fees[i]`, the counter
bumped. -/
theorem rx_al_feeTl {σ : Stor} {W : Devm → Prop} {F AF N dif f st af : B256}
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 fin : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hi : i < 3) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0xaa0) (hctr : WordAt img 0xa40 (Nat.toB256 i)) (hF : WordAt img 0x1a0 F)
    (hAF : WordAt img 0x1c0 AF) (hdif : WordAt img 0xa80 dif)
    (hN : WordAt img (0x460 + 32 * i) N)
    (hm2 : F.Nofm dif) (hf : f = F * dif / rliDen) (hm3 : f.Nofm AF)
    (hs3 : ¬ N < f * AF / rliDen) (hst : st = N - f * AF / rliDen) (hs4 : ¬ N < f)
    (haf : af = N - f) (hG : R + 26000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 i) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xaa0 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x140 + 32 * i) ∨
        (0x160 + 32 * i ≤ o ∧ o + 32 ≤ 0x460 + 32 * i) ∨ (0x480 + 32 * i ≤ o ∧ o + 32 ≤ 0xa40) ∨
        0xa60 ≤ o → WordAt img' o w) →
      WordAt img' (0x140 + 32 * i) f → WordAt img' (0x460 + 32 * i) af →
      WordAt img' 0xa40 (Nat.toB256 (i + 1)) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x14, 0x09] ::
        B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: 0xa40 :: S) M' g) fin Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M G)
      (alFeeTl a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 fin) Q := by
  subst hf hst haf
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 505 := ⟨G - 505, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1a0) (v := F) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hF) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa80) (v := dif) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hdif) (by hrs) ·)
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
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm2) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreK (o := 0x140 + 32 * i) hR hW hsz (al_off hi 0x140 (by decide) _ (by decide)) ⟨by omega, by decide⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x460 + 32 * i) (v := N) hR hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by wautoH hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x140 + 32 * i) hR hsz (al_off hi 0x140 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1c0) (v := AF) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hAF) (by hrs) ·)
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
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm3) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
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
  xr (rx_branch_succ (ex_geGuard hs3) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreK (o := 0xc0) hR hW hsz rfl ⟨by decide, by decide⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22; replace hL := hL.sstoreE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 182 := ⟨g2 - 182, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x460 + 32 * i) (v := N) hR hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by wautoH hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x140 + 32 * i) hR hsz (al_off hi 0x140 (by decide) _ (by decide)) ⟨by omega, by decide⟩ (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs4) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreK (o := 0x460 + 32 * i) hR hW hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, by decide⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
  xr (rx_pop ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa40) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreK (o := 0xa40) hR hW hsz rfl ⟨by decide, by decide⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  rw [succ_lit hi] at hR ⊢
  exact k _ M _ _ hL hR hW hsz (fun o v h ho => by wautoH h)
    (by
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      exact WordAt.write_self _ _ _)
    (by
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      exact WordAt.write_self _ _ _)
    (by wauto) (by omega) (by omega)

end Fee

end Blanc.Lift.Curve3Pool
