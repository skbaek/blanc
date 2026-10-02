import Blanc.Lift.ExactWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.Vyper
import Blanc.Lift.UniswapV2Pair.Cert
/-! Actual checked arithmetic cuts 59/72 and their common return 9. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune
theorem checked_return_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {x y z ρ : B256} :
    SFunc.RunExact cert.prog sevm (St b (z :: y :: x :: ρ :: R) M (G + 19))
      t_0df6_c9 (.returned (St b (z :: R) M G)) := by
  unfold t_0df6_c9
  apply rx_dest
  apply rx_swap (S' := ρ :: y :: x :: z :: R) rfl
  apply rx_swap (S' := x :: y :: ρ :: z :: R) rfl
  apply rx_pop
  apply rx_pop
  exact rx_ret

theorem sub59_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} (cover : y ≤ x) (room : R.length ≤ 1018) :
    SFunc.RunExact cert.prog sevm (St b (y :: x :: ρ :: R) M (G + 54))
      t_226e_c59 (.returned (St b ((x - y) :: R) M G)) := by
  have hgt : B256.gtCheck (x - y) x = 0 := by
    apply ite_eq_right
    change ¬ x < x - y
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_sub_eq_of_le x y cover]
    omega
  unfold t_226e_c59
  apply rx_dest
  apply rx_dup (w := y) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x) rfl (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x - y) rfl (by simp only [List.length_cons]; omega)
  apply rx_gt hgt (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x0df6) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) (g := t_0df6_c9) rfl
  exact checked_return_exact

theorem add72_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} (nowrap : x.toNat + y.toNat < 2 ^ 256) (room : R.length ≤ 1018) :
    SFunc.RunExact cert.prog sevm (St b (y :: x :: ρ :: R) M (G + 54))
      t_2abc_c72 (.returned (St b ((x + y) :: R) M G)) := by
  have hlt : B256.ltCheck (x + y) x = 0 := by
    exact ite_eq_right ((B256.nof_iff_not_add_lt x y).mp nowrap)
  unfold t_2abc_c72
  apply rx_dest
  apply rx_dup (w := y) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x) rfl (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := x + y) rfl (by simp only [List.length_cons]; omega)
  apply rx_lt hlt (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x0df6) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) (g := t_0df6_c9) rfl
  exact checked_return_exact

/-- The literal shared arithmetic return discards its two original operands. -/
theorem checked_return_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y z ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (z :: y :: x :: ρ :: R) M G) t_0df6_c9 o) :
    ∃ G', o = .returned (St b (z :: R) M G') := by
  have h := run.cut
  unfold t_0df6_c9 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := ρ :: y :: x :: z :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := x :: y :: ρ :: z :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨G', hg⟩ := ric_ret h
  exact ⟨G', Seg.done.inj hg⟩

/-- Successful checked subtraction derives cover and can only return normally. -/
theorem sub59_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (y :: x :: ρ :: R) M G) t_226e_c59 o) :
    y ≤ x ∧ ∃ G', o = .returned (St b ((x - y) :: R) M G') := by
  have h := run.cut
  unfold t_226e_c59 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := x - y) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_gt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo (g := t_0df6_c9) (by decide : 9 ∉ []) rfl h with
    ⟨_, _, hf⟩ | ⟨hw, _, hs⟩
  · exact (hf.false_of_noOk (by decide : t_227a_c59.noOk = true)).elim
  · have hcmp := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    have cover : y ≤ x := by
      rw [B256.le_iff_toNat_le_toNat]
      by_contra hn
      have hx := B256.toNat_lt x
      have hy := B256.toNat_lt y
      have hb : 2 ^ 256 + x.toNat - y.toNat < 2 ^ 256 := by omega
      rw [B256.toNat_sub, Nat.lo, Nat.mod_eq_of_lt hb] at hcmp
      omega
    exact ⟨cover, checked_return_inv hs.uncut⟩

/-- Successful checked addition derives no-wrap and excludes its revert arm. -/
theorem add72_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {x y ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (y :: x :: ρ :: R) M G) t_2abc_c72 o) :
    x.toNat + y.toNat < 2 ^ 256 ∧
      ∃ G', o = .returned (St b ((x + y) :: R) M G') := by
  have h := run.cut
  unfold t_2abc_c72 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := x + y) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_lt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo (g := t_0df6_c9) (by decide : 9 ∉ []) rfl h with
    ⟨_, _, hf⟩ | ⟨hw, _, hs⟩
  · exact (hf.false_of_noOk (by decide : t_2ac8_c72.noOk = true)).elim
  · have hcmp := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    have nowrap : x.toNat + y.toNat < 2 ^ 256 := by
      apply (B256.nof_iff_not_add_lt x y).mpr
      rw [B256.lt_iff_toNat_lt_toNat]
      omega
    exact ⟨nowrap, checked_return_inv hs.uncut⟩

end Blanc.Lift.UniswapV2Pair
