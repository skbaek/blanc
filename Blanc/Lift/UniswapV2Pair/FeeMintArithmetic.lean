import Blanc.Lift.UniswapV2Pair.WriterArithmetic
import Blanc.Lift.InvWalkProvenance
import Jaune.RPow
/-! The literal checked multiplication cuts consumed by fee68. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Actual multiplication overflow join, with its successful flag. -/
theorem mul_return_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y z ρ : B256} (room : R.length ≤ 1018) :
    SFunc.RunExact cert.prog sevm (St b (1 :: z :: y :: x :: ρ :: R) M (G + 33))
      t_2203_c18 (.returned (St b (z :: R) M G)) := by
  unfold t_2203_c18
  apply rx_dest
  apply rx_push (w := 0x0df6) rfl (by simp only [List.length_cons]; omega)
  apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) (g := t_0df6_c9) rfl
  exact checked_return_exact

/-- Nonzero multiplier path, including the actual denominator test and overflow join. -/
theorem mul_body_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} (hy : y ≠ 0) (nowrap : B256.Nofm x y)
    (room : R.length ≤ 1015) :
    SFunc.RunExact cert.prog sevm (St b (0 :: 0 :: y :: x :: ρ :: R) M (G + 82))
      t_21f2_c58 (.returned (St b ((x * y) :: R) M G)) := by
  have division : (x * y) / y = x := (B256.mul_div_eq_iff_nofm hy).mpr nowrap
  unfold t_21f2_c58
  apply rx_pop
  apply rx_pop
  apply rx_dup (w := y) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x) rfl (by simp only [List.length_cons]; omega)
  apply rx_mul (v := x * y) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := y) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x * y) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := y) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2200) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ hy
  unfold t_2200_c58
  apply rx_dest
  apply rx_div division (by simp only [List.length_cons]; omega)
  apply rx_eq (v := 1) (by exact ite_eq_left rfl)
    (by simp only [List.length_cons]; omega)
  exact mul_return_exact (by omega)

/-- Exact charge distinguishes the literal zero multiplier shortcut. -/
def mul58Charge (y : B256) : Nat := if y = 0 then 59 else 108

/-- The actual checked multiplication entry with its full raw state preserved. -/
theorem mul58_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} (nowrap : B256.Nofm x y) (room : R.length ≤ 1015) :
    SFunc.RunExact cert.prog sevm (St b (y :: x :: ρ :: R) M (G + mul58Charge y))
      t_21e8_c58 (.returned (St b ((x * y) :: R) M G)) := by
  by_cases hy : y = 0
  · subst y
    have product : x * (0 : B256) = 0 := by
      apply B256.toNat_inj
      rw [B256.toNat_mul, B256.toNat_zero, Nat.mul_zero]
      rfl
    rw [product]
    simp only [mul58Charge, ite_eq_left]
    unfold t_21e8_c58
    apply rx_dest
    apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_dup1 (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x2203) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) (g := t_2203_c18) rfl
    exact mul_return_exact (by omega)
  · simp only [mul58Charge, ite_eq_right hy]
    unfold t_21e8_c58
    apply rx_dest
    apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := y) rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (by simp only [B256.eqCheck, ite_eq_right hy])
      (by simp only [List.length_cons]; omega)
    apply rx_dup1 (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x2203) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    exact mul_body_exact hy nowrap room

/-- Success at the literal overflow join derives its flag and normal raw return. -/
theorem mul_return_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y z flag ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (flag :: z :: y :: x :: ρ :: R) M G)
      t_2203_c18 o) :
    flag ≠ 0 ∧ ∃ G', o = .returned (St b (z :: R) M G') := by
  have h := run.cut
  unfold t_2203_c18 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branchTo (g := t_0df6_c9) (by decide : 9 ∉ []) rfl h with
    ⟨_, _, failed⟩ | ⟨accepted, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_2208_c18.noOk = true)).elim
  · exact ⟨accepted, checked_return_inv body.uncut⟩

/-- The actual nonzero multiplication path derives no-wrap from its quotient check. -/
theorem mul_body_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y a z ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (a :: z :: y :: x :: ρ :: R) M G)
      t_21f2_c58 o) :
    y ≠ 0 ∧ B256.Nofm x y ∧ ∃ G', o = .returned (St b ((x * y) :: R) M G') := by
  have h := run.cut
  unfold t_21f2_c58 at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mul hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := x * y) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branch h with ⟨_, _, failed⟩ | ⟨hy, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_21ff_c58.noOk = true)).elim
  · unfold t_2200_c58 at body
    obtain ⟨_, body⟩ := ric_dest body
    obtain ⟨_, hs, body⟩ := ric_next body; obtain ⟨_, rfl⟩ := ri_div hs
    obtain ⟨_, hs, body⟩ := ric_next body; obtain ⟨_, rfl⟩ := ri_eq hs
    obtain ⟨flag, returned⟩ := mul_return_inv body.uncut
    have division : (x * y) / y = x := by
      by_contra hn
      rw [B256.eqCheck, ite_eq_right hn] at flag
      exact flag rfl
    exact ⟨hy, (B256.mul_div_eq_iff_nofm hy).mp division, returned⟩

/-- Successful entry58 derives multiplication no-wrap, including its zero shortcut. -/
theorem mul58_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (y :: x :: ρ :: R) M G) t_21e8_c58 o) :
    B256.Nofm x y ∧ ∃ G', o = .returned (St b ((x * y) :: R) M G') := by
  have h := run.cut
  unfold t_21e8_c58 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branchTo (g := t_2203_c18) (by decide : 18 ∉ []) rfl h with
    ⟨_, _, body⟩ | ⟨accepted, _, body⟩
  · exact (mul_body_inv body.uncut).2
  · have hy : y = 0 := by
      by_contra hn
      rw [B256.eqCheck, ite_eq_right hn] at accepted
      exact accepted rfl
    subst y
    have product : x * (0 : B256) = 0 := by
      apply B256.toNat_inj
      rw [B256.toNat_mul, B256.toNat_zero, Nat.mul_zero]
      rfl
    have nowrap : B256.Nofm x 0 := by
      unfold B256.Nofm
      rw [B256.toNat_zero, Nat.mul_zero]
      exact Nat.two_pow_pos 256
    have returned := (mul_return_inv body.uncut).2
    rw [product]
    exact ⟨nowrap, returned⟩

end Blanc.Lift.UniswapV2Pair
