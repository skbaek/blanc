import Blanc.Lift.UniswapV2Pair.FeeMintSource
import Blanc.Lift.UniswapV2Pair.UpdateSource

/-! Complete literal post-fee mint suffix, including both liquidity pricing arms. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal min70 compares the right operand to the left operand. -/
def mintMinWord (left right : B256) : B256 := if right < left then right else left

/-- The min70 return drops both operands and its zero temporary. -/
theorem mintMinReturn_inv {sevm : Sevm} {b : Devm} {R : List B256}
    {C : List Nat} {M : Mem} {G : Nat} {value left right ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (value :: 0 :: left :: right :: ρ :: R) M G) t_298b_c27 r) :
    ∃ gas, r = .done (.returned (St b (value :: R) M gas)) := by
  unfold t_298b_c27 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := ρ :: 0 :: left :: right :: value :: R) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := right :: 0 :: left :: ρ :: value :: R) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  exact ric_ret run

/-- The shared min70 cleanup costs21gas. -/
theorem mintMinReturn_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {value left right ρ : B256} :
    SFunc.RunExact cert.prog sevm
      (St b (value :: 0 :: left :: right :: ρ :: R) M (G + 21)) t_298b_c27
      (.returned (St b (value :: R) M G)) := by
  unfold t_298b_c27
  apply rx_dest
  apply rx_swap (S' := ρ :: 0 :: left :: right :: value :: R) rfl
  apply rx_swap (S' := right :: 0 :: left :: ρ :: value :: R) rfl
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- Invert both actual min70 arms, retaining the complete untouched suffix. -/
theorem mintMin70_inv {sevm : Sevm} {b : Devm} {R : List B256}
    {C : List Nat} {M : Mem} {G : Nat} {left right ρ : B256} {r : Seg}
    (h27 : 27 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (left :: right :: ρ :: R) M G) t_297a_c70 r) :
    ∃ gas, r = .done (.returned (St b (mintMinWord left right :: R) M gas)) := by
  unfold t_297a_c70 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := left) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := right) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_lt hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  by_cases less : right < left
  · simp only [B256.ltCheck, ite_eq_left less] at run
    rcases ric_branch run with ⟨zero, _, _⟩ | ⟨_, _, run⟩
    · exact (by decide : (1 : B256) ≠ 0) zero |>.elim
    · unfold t_2989_c70 at run
      obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨_, hs, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (w := right) rfl hs
      simpa only [mintMinWord, ite_eq_left less] using mintMinReturn_inv run
  · simp only [B256.ltCheck, ite_eq_right less] at run
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨zero, _, _⟩
    · unfold t_2984_c70 at run
      obtain ⟨_, hs, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (w := left) rfl hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, run⟩ := ric_jump (g := t_298b_c27) h27 rfl run
      simpa only [mintMinWord, ite_eq_right less] using mintMinReturn_inv run
    · exact (zero rfl).elim

/-- Literal min70 charge distinguishes the fallthrough jump from the taken arm. -/
def mintMin70Gas (left right : B256) : Nat := if right < left then 51 else 61

theorem mintMin70_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {left right ρ : B256} (room : R.length ≤ 1018) :
    SFunc.RunExact cert.prog sevm
      (St b (left :: right :: ρ :: R) M (G + mintMin70Gas left right)) t_297a_c70
      (.returned (St b (mintMinWord left right :: R) M G)) := by
  unfold t_297a_c70
  by_cases less : right < left
  · simp only [mintMin70Gas, mintMinWord, ite_eq_left less]
    apply rx_dest
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := left) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := right) rfl (by simp only [List.length_cons]; omega)
    apply rx_lt (v := 1) (by simp only [B256.ltCheck, ite_eq_left less])
      (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    unfold t_2989_c70
    apply rx_dest
    apply rx_dup (w := right) rfl (by simp only [List.length_cons]; omega)
    exact mintMinReturn_exact
  · simp only [mintMin70Gas, mintMinWord, ite_eq_right less]
    apply rx_dest
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := left) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := right) rfl (by simp only [List.length_cons]; omega)
    apply rx_lt (v := 0) (by simp only [B256.ltCheck, ite_eq_right less])
      (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_zero
    unfold t_2984_c70
    apply rx_dup (w := left) rfl (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    exact rx_jump rfl mintMinReturn_exact

/-- The later pricing arm consumes min70 and installs its actual result in the cached liquidity slot. -/
theorem mintLaterFinish_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {numerator1 denominator1 floor0 supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (numerator1 :: denominator1 :: floor0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_12c4_c41 r) :
    ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        mintMinWord (numerator1 / denominator1) floor0 :: toWord :: ρ :: R) M gas) t_12cd_c11 r := by
  unfold t_12c4_c41 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_div hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, call⟩ := ric_call (g := t_297a_c70) rfl run
  rcases call with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, eq⟩ := mintMin70_inv (by decide : 27 ∉ ([] : List Nat)) callee.cut
    cases eq
    unfold t_12ca_c41 at tail
    obtain ⟨_, tail⟩ := ric_dest tail
    obtain ⟨_, hs, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_swap (S' := oldLiquidity :: supply :: f :: amount1 :: amount0 ::
      b1 :: b0 :: r1 :: r0 :: mintMinWord (numerator1 / denominator1) floor0 :: toWord :: ρ :: R) rfl hs
    obtain ⟨_, hs, tail⟩ := ric_next tail; obtain ⟨_, rfl⟩ := ri_pop hs
    exact ⟨_, tail⟩
  · obtain ⟨_, eq⟩ := mintMin70_inv (by decide : 27 ∉ ([] : List Nat)) callee.cut
    cases eq

/-- Both exact min70 arms feed the same real12cd continuation after6gas cleanup. -/
theorem mintLaterFinish_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {numerator1 denominator1 floor0 supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (room : R.length ≤ 1007)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        mintMinWord (numerator1 / denominator1) floor0 :: toWord :: ρ :: R) M G) t_12cd_c11 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (numerator1 :: denominator1 :: floor0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + 23 + mintMin70Gas (numerator1 / denominator1) floor0)) t_12c4_c41 r := by
  have tail : SFunc.RunExactCut cert.prog sevm C
      (St b (mintMinWord (numerator1 / denominator1) floor0 :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M (G + 6)) t_12ca_c41 r := by
    unfold t_12ca_c41
    apply rxc_dest
    apply rxc_swap (S' := oldLiquidity :: supply :: f :: amount1 :: amount0 ::
      b1 :: b0 :: r1 :: r0 :: mintMinWord (numerator1 / denominator1) floor0 :: toWord :: ρ :: R) rfl
    exact rxc_pop body
  unfold t_12c4_c41
  rw [show G + 23 + mintMin70Gas (numerator1 / denominator1) floor0 =
    (G + 6 + mintMin70Gas (numerator1 / denominator1) floor0) + 17 from by omega]
  apply rxc_dest
  apply rxc_div rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_297a_c70) rfl
    (mintMin70_exact (by simp only [List.length_cons]; omega)) tail

/-- The first later-supply checked product uses the sampled supply and amount0. -/
theorem mintLaterProduct0_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (bound0 : r0.toNat < 2 ^ 112)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_1270_c41 r) :
    B256.Nofm amount0 supply ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((amount0 * supply) :: r0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M gas) t_1294_c41 r := by
  unfold t_1270_c41 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [show r0 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = r0 from feeReserveWord_eq bound0] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := amount0) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := supply) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, call⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases call with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨nowrap, _, eq⟩ := mul58_inv callee
    cases eq
    exact ⟨nowrap, _, tail⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq

/-- The checked amount1 product follows the real first floor division. -/
theorem mintLaterProduct1_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {product0 supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (product0 :: r0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_129b_c41 r) :
    B256.Nofm amount1 supply ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((amount1 * supply) :: r1 :: (product0 / r0) :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M gas) t_12bd_c41 r := by
  unfold t_129b_c41 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_div hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [show r1 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = r1 from feeReserveWord_eq bound1] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := amount1) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := supply) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, call⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases call with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨nowrap, _, eq⟩ := mul58_inv callee
    cases eq
    exact ⟨nowrap, _, tail⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq

/-- Invert the complete later-supply pricing arm: both checked products, both real divisor guards and min70. -/
theorem mintLaterPrice_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_1270_c41 r) :
    B256.Nofm amount0 supply ∧ r0 ≠ 0 ∧ B256.Nofm amount1 supply ∧ r1 ≠ 0 ∧
      ∃ gas, SFunc.RunCut cert.prog sevm C
        (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
          mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0) :: toWord :: ρ :: R) M gas)
        t_12cd_c11 r := by
  obtain ⟨product0, _, run⟩ := mintLaterProduct0_inv bound0 run
  unfold t_1294_c41 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branch run with ⟨_, _, bad⟩ | ⟨nonzero0, _, run⟩
  · exact (bad.false_of_noOk (by decide : t_129a_c41.noOk = true)).elim
  · obtain ⟨product1, _, run⟩ := mintLaterProduct1_inv bound1 run
    unfold t_12bd_c41 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    rcases ric_branch run with ⟨_, _, bad⟩ | ⟨nonzero1, _, run⟩
    · exact (bad.false_of_noOk (by decide : t_12c3_c41.noOk = true)).elim
    · obtain ⟨gas, run⟩ := mintLaterFinish_inv run
      exact ⟨product0, nonzero0, product1, nonzero1, gas, run⟩


/-- Exact first checked product uses the literal reserve mask and actual sampled supply. -/
theorem mintLaterProduct0_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (product : B256.Nofm amount0 supply) (room : R.length ≤ 1000)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b ((amount0 * supply) :: r0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_1294_c41 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + mul58Charge supply + 39)) t_1270_c41 r := by
  unfold t_1270_c41
  apply rxc_dest
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_and (feeReserveWord_eq bound0) (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := amount0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := supply) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_and rfl (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_21e8_c58) rfl
    (mul58_exact product (by simp only [List.length_cons]; omega)) body

/-- Exact second checked product follows the actual first floor division and reserve mask. -/
theorem mintLaterProduct1_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {product0 supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (bound1 : r1.toNat < 2 ^ 112) (product : B256.Nofm amount1 supply) (room : R.length ≤ 1000)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b ((amount1 * supply) :: r1 :: (product0 / r0) :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_12bd_c41 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (product0 :: r0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + mul58Charge supply + 41)) t_129b_c41 r := by
  unfold t_129b_c41
  apply rxc_dest
  apply rxc_div rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rxc_and (feeReserveWord_eq bound1) (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := amount1) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := supply) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_and rfl (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_21e8_c58) rfl
    (mul58_exact product (by simp only [List.length_cons]; omega)) body

/-- Exact complete later pricing consumes both genuine nonzero guards and the concrete min70 result. -/
theorem mintLaterPrice_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (product0 : B256.Nofm amount0 supply) (product1 : B256.Nofm amount1 supply)
    (nonzero0 : r0 ≠ 0) (nonzero1 : r1 ≠ 0) (room : R.length ≤ 1000)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0) :: toWord :: ρ :: R) M G)
      t_12cd_c11 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + 137 + mul58Charge supply + mul58Charge supply +
          mintMin70Gas ((amount1 * supply) / r1) ((amount0 * supply) / r0))) t_1270_c41 r := by
  let minCost := mintMin70Gas ((amount1 * supply) / r1) ((amount0 * supply) / r0)
  have finish := mintLaterFinish_exact (oldLiquidity := oldLiquidity) (by omega : R.length ≤ 1007) body
  have guarded1 : SFunc.RunExactCut cert.prog sevm C
      (St b ((amount1 * supply) :: r1 :: ((amount0 * supply) / r0) :: 0x12ca :: supply :: f ::
        amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + 40 + minCost)) t_12bd_c41 r := by
    unfold t_12bd_c41
    rw [show G + 40 + minCost = (G + 23 + minCost) + 17 from by omega]
    apply rxc_dest
    apply rxc_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
    apply rxc_push rfl (by simp only [List.length_cons]; omega)
    exact rxc_branch_succ nonzero1 finish
  have productRun1 := mintLaterProduct1_exact bound1 product1 room guarded1
  have guarded0 : SFunc.RunExactCut cert.prog sevm C
      (St b ((amount0 * supply) :: r0 :: 0x12ca :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + 98 + minCost + mul58Charge supply)) t_1294_c41 r := by
    unfold t_1294_c41
    rw [show G + 98 + minCost + mul58Charge supply = (G + 40 + minCost + mul58Charge supply + 41) + 17 from by omega]
    apply rxc_dest
    apply rxc_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
    apply rxc_push rfl (by simp only [List.length_cons]; omega)
    exact rxc_branch_succ nonzero0 productRun1
  have first := mintLaterProduct0_exact bound0 product0 room guarded0
  rw [show G + 137 + mul58Charge supply + mul58Charge supply +
      mintMin70Gas ((amount1 * supply) / r1) ((amount0 * supply) / r0) =
      (G + 98 + minCost + mul58Charge supply) + mul58Charge supply + 39 from by omega]
  exact first

/-- Initial pricing starts with the actual amount product, before the context-specific sqrt69 call. -/
theorem mintInitialProduct_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_123f_c41 r) :
    B256.Nofm amount0 amount1 ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((amount0 * amount1) :: 0x0bfd :: 1000 :: 0x125c :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M gas) t_1257_c41 r := by
  unfold t_123f_c41 at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := amount0) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := amount1) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, call⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases call with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨nowrap, _, eq⟩ := mul58_inv callee
    cases eq
    exact ⟨nowrap, _, tail⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq

/-- The initial arm consumes the real1257_c41 root and checked1000 subtraction. -/
theorem mintInitialRootSub_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {product supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (product :: 0x0bfd :: 1000 :: 0x125c :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_1257_c41 r) :
    (1000 : B256) ≤ (Nat.sqrt product.toNat).toB256 ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b (((Nat.sqrt product.toNat).toB256 - 1000) :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M gas) t_125c_c41 r := by
  unfold t_1257_c41 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, call⟩ := ric_call (g := t_2878_c69) rfl run
  rcases call with ⟨d, callee, run⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, eq⟩ := sqrt_of_run callee
    cases eq
    unfold t_0bfd_c41 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
    dsimp only [List.set] at run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
    obtain ⟨_, sub⟩ := ric_call (g := t_226e_c59) rfl run
    rcases sub with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
    · obtain ⟨cover, _, eq⟩ := sub59_inv callee
      cases eq
      exact ⟨cover, _, tail⟩
    · obtain ⟨_, _, eq⟩ := sub59_inv callee
      cases eq
  · obtain ⟨_, eq⟩ := sqrt_of_run callee
    cases eq


/-- Exact actual initial sqrt69 and checked subtraction feed the true125c minimum caller. -/
theorem mintInitialRootSub_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {product supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (cover : (1000 : B256) ≤ (Nat.sqrt product.toNat).toB256) (room : R.length ≤ 1000)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b (((Nat.sqrt product.toNat).toB256 - 1000) :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_125c_c41 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (product :: 0x0bfd :: 1000 :: 0x125c :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + 87 + sqrtCharge product.toNat)) t_1257_c41 r := by
  have tail : SFunc.RunExactCut cert.prog sevm C
      (St b ((Nat.sqrt product.toNat).toB256 :: 1000 :: 0x125c :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M (G + 75)) t_0bfd_c41 r := by
    unfold t_0bfd_c41
    apply rxc_dest
    apply rxc_swap (S' := 1000 :: (Nat.sqrt product.toNat).toB256 :: 0x125c :: supply :: f ::
      amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) rfl
    apply rxc_push rfl (by simp only [List.length_cons]; omega)
    apply rxc_push rfl (by simp only [List.length_cons]; omega)
    apply rxc_and rfl (by simp only [List.length_cons]; omega)
    exact rxc_callRet (g := t_226e_c59) rfl
      (sub59_exact cover (by simp only [List.length_cons]; omega)) body
  unfold t_1257_c41
  rw [show G + 87 + sqrtCharge product.toNat = (G + 75 + sqrtCharge product.toNat) + 12 from by omega]
  apply rxc_dest
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_2878_c69) rfl
    (sqrt_exact (by simp only [List.length_cons]; omega)) tail

/-- Both real arithmetic callees construct the initial price with exact selected multiplication and sqrt charges. -/
theorem mintInitialPrice_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (product : B256.Nofm amount0 amount1)
    (cover : (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256) (room : R.length ≤ 1000)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b (((Nat.sqrt (amount0 * amount1).toNat).toB256 - 1000) :: supply :: f :: amount1 :: amount0 ::
        b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G) t_125c_c41 r) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + 122 + sqrtCharge (amount0 * amount1).toNat + mul58Charge amount1)) t_123f_c41 r := by
  unfold t_123f_c41
  rw [show G + 122 + sqrtCharge (amount0 * amount1).toNat + mul58Charge amount1 =
    (G + 87 + sqrtCharge (amount0 * amount1).toNat + mul58Charge amount1) + 35 from by omega]
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := amount0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := amount1) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_push rfl (by simp only [List.length_cons]; omega)
  apply rxc_and rfl (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_21e8_c58) rfl
    (mul58_exact product (by simp only [List.length_cons]; omega)) (mintInitialRootSub_exact cover room body)

/-- Initial-price acceptance is derived from both arithmetic callees, with its real minimum-mint continuation. -/
theorem mintInitialPrice_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_123f_c41 r) :
    B256.Nofm amount0 amount1 ∧ (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256 ∧
      ∃ gas, SFunc.RunCut cert.prog sevm C
        (St b (((Nat.sqrt (amount0 * amount1).toNat).toB256 - 1000) :: supply :: f :: amount1 :: amount0 ::
          b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M gas) t_125c_c41 r := by
  obtain ⟨product, _, run⟩ := mintInitialProduct_inv run
  obtain ⟨cover, gas, tail⟩ := mintInitialRootSub_inv run
  exact ⟨product, cover, gas, tail⟩

def mintEventTopic : B256 :=
  0x4c209b5fc8ad50758f13e2e1088ba56a560dff690a1c6fef26394f4c03821c4f

def mintEventMemory (M : Mem) (amount0 amount1 : B256) : Mem :=
  (M.write 128 amount0.toBytes).write 160 amount1.toBytes

def mintEventLog (sevm : Sevm) (amount0 amount1 : B256) : Jaune.Log :=
  ⟨sevm.currentTarget, [mintEventTopic, sevm.caller.toB256], amount0.toBytes ++ amount1.toBytes⟩

def mintReturnWorld (sevm : Sevm) (b : Devm) (amount0 amount1 : B256) : Devm :=
  afterSstore sevm (b.addLog (mintEventLog sevm amount0 amount1)) 12 1

/-- Exact complete Mint LOG2, actual unlock write and public-function internal return. -/
theorem mintReturn_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G unlockCost : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1007)
    (unlockCharge : unlockCost = sstoreCost sevm
      (b.addLog (mintEventLog sevm amount0 amount1)) 12 1)
    (unlockSentry : gCallStipend < G + unlockCost + 31) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        liquidity :: toWord :: ρ :: R) M (G + unlockCost + 1747)) t_137e_c12
      (.returned (St (mintReturnWorld sevm b amount0 amount1) (liquidity :: R)
        (mintEventMemory M amount0 amount1) G)) := by
  have m1 := mem.write 128 amount0 (Or.inr (by decide))
  rw [show memExtSize 192 128 32 = 192 from by decide] at m1
  have m2 := m1.write 160 amount1 (Or.inr (by decide))
  rw [show memExtSize 192 160 32 = 192 from by decide] at m2
  unfold t_137e_c12
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  apply rx_dup (w := amount0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup (w := amount1) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq m1.size]; decide
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ m2.word (m2.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl,
      show (160 : B256).toNat = 160 from rfl]
    rw [St.extCost_eq m2.size]; decide
  apply rx_caller (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := mintEventTopic) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 64) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  rw [show G + unlockCost + 1678 = (G + unlockCost + 41) + 1637 from by omega]
  refine rx_log2 (c := 1637) (data := amount0.toBytes ++ amount1.toBytes) nonstatic ?_
    (Mem.read_two_word_writes_at_raw M 128 amount0 amount1) (m2.read_self (by decide)) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl,
      show (160 : B256).toNat = 160 from rfl]
    rw [St.extCost_eq m2.size]; decide
  apply rx_pop
  apply rx_pop
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + unlockCost + 31 = (G + 31) + unlockCost from by omega]
  apply rx_sstoreC fork unlockCharge (by omega) nonstatic
  apply rx_pop
  apply rx_swap (S' := liquidity :: b1 :: b0 :: r1 :: r0 :: amount0 :: toWord :: ρ :: R) rfl
  apply rx_swap (S' := ρ :: b1 :: b0 :: r1 :: r0 :: amount0 :: toWord :: liquidity :: R) rfl
  apply rx_swap (S' := toWord :: b1 :: b0 :: r1 :: r0 :: amount0 :: ρ :: liquidity :: R) rfl
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- Invert the complete Mint log/unlock/return, preserving the actual full world. -/
theorem mintReturn_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        liquidity :: toWord :: ρ :: R) M G) t_137e_c12 o) :
    sevm.isStatic = false ∧ ∃ gas,
      o = .returned (St (mintReturnWorld sevm b amount0 amount1) (liquidity :: R)
        (mintEventMemory M amount0 amount1) gas) := by
  have m1 := mem.write 128 amount0 (Or.inr (by decide))
  rw [show memExtSize 192 128 32 = 192 from by decide] at m1
  have m2 := m1.write 160 amount1 (Or.inr (by decide))
  rw [show memExtSize 192 160 32 = 192 from by decide] at m2
  have ptr0 := mem.word
  have ptr2 := m2.word
  dsimp only [memWord] at ptr0 ptr2
  have h := run.cut
  unfold t_137e_c12 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [0x40] = (64 : B256) from by decide] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, h⟩ := ric_next h; obtain ⟨_, eq⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, ptr0, mem.read_self (by decide)] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hs
  simp only [show (128 : B256).toNat = 128 from rfl] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_val (w := 160) (by decide) (ri_add hs)
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hs
  simp only [show (160 : B256).toNat = 160 from rfl] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, h⟩ := ric_next h; obtain ⟨_, eq⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, ptr2, m2.read_self (by decide)] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_caller hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_sub hs)
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_val (w := 64) (by decide) (ri_add hs)
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  clear * - h fork mem m1 m2
  obtain ⟨d, logStep, h⟩ := ric_next h
  obtain ⟨_, eq⟩ := ri_log2_post logStep
  rw [show (128 : B256).toNat = 128 from rfl,
    show (64 : B256).toNat = 64 from rfl,
    m2.read_self (by decide : 128 + 64 ≤ 192),
    Mem.read_two_word_writes_at_raw] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hs
  obtain ⟨_, rfl⟩ := ri_sstore fork hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨gas, eq⟩ := ric_ret h
  refine ⟨nonstatic, gas, ?_⟩
  exact Seg.done.inj eq

def mintKLastWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 8) 11
    (reserve0Read (b.getStorVal sevm.currentTarget 8) * reserve1Read (b.getStorVal sevm.currentTarget 8))

def mintConditionalLastWorld (sevm : Sevm) (b : Devm) (f : B256) : Devm :=
  if f = 0 then b else mintKLastWorld sevm b

/-- The fee-on suffix reads the UPDATED slot8 before checked multiplication and writes the actual product to11. -/
theorem mintKLast_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M G)
      t_1343_c11 r) :
    sevm.isStatic = false ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St (mintKLastWorld sevm b)
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M gas)
      t_137e_c12 r := by
  unfold t_1343_c11 at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_div hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, call⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases call with ⟨d, callee, run⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq
    unfold t_137a_c11 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    obtain ⟨_, hs, run⟩ := ric_next run
    have mutable := ri_sstore_nonstatic fork hs
    obtain ⟨_, rfl⟩ := ri_sstore fork hs
    exact ⟨mutable, _, run⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq


/-- The actual updated slot8 masks bound both operands of the kLast checked product. -/
theorem mintKLastProduct_noWrap (word : B256) : B256.Nofm (reserve0Read word) (reserve1Read word) := by
  have low (x : B256) : (x &&& reserveMask112).toNat < 2 ^ 112 := by
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from by decide]
    rw [PackedWord.lowMask_toNat x (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  exact feeReserveProduct_noWrap (low word) (low (word / reserveDiv112))

/-- Exact fee-on kLast suffix charges the current updated slot8 and actual subsequent store11. -/
theorem mintKLast_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G loadCost storeCost : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1000)
    (loadCharge : loadCost = sloadCost sevm b 8)
    (storeCharge : storeCost = sstoreCost sevm (afterSload sevm b 8) 11
      (reserve0Read (b.getStorVal sevm.currentTarget 8) * reserve1Read (b.getStorVal sevm.currentTarget 8)))
    (sentry : gCallStipend < G + storeCost)
    (body : SFunc.RunExact cert.prog sevm
      (St (mintKLastWorld sevm b)
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M G)
      t_137e_c12 o) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        M (G + loadCost + storeCost + mul58Charge (reserve1Read (b.getStorVal sevm.currentTarget 8)) + 59))
      t_1343_c11 o := by
  let word := b.getStorVal sevm.currentTarget 8
  have tail : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8) ((reserve0Read word * reserve1Read word) :: supply :: f :: amount1 ::
        amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M (G + storeCost + 4))
      t_137a_c11 o := by
    unfold t_137a_c11
    apply rx_dest
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    exact rx_sstoreC fork storeCharge sentry nonstatic body
  unfold t_1343_c11
  rw [show G + loadCost + storeCost + mul58Charge (reserve1Read word) + 59 =
    ((G + storeCost + 4 + mul58Charge (reserve1Read word) + 52) + loadCost) + 3 from by omega]
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork loadCharge (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_21e8_c58) rfl
    (mul58_exact (mintKLastProduct_noWrap word) (by simp only [List.length_cons]; omega)) tail

/-- Complete post-update conditional kLast, Mint log, unlock and return, including fee-off. -/
theorem mintAfterUpdate_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M G)
      t_133c_c11 o) :
    sevm.isStatic = false ∧ ∃ gas,
      o = .returned (St (mintReturnWorld sevm (mintConditionalLastWorld sevm b f) amount0 amount1)
        (liquidity :: R) (mintEventMemory M amount0 amount1) gas) := by
  have h := run.cut
  unfold t_133c_c11 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := f) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  by_cases off : f = 0
  · simp only [B256.eqCheck, ite_eq_left off] at h
    rcases ric_branchTo (g := t_137e_c12) (by decide : 12 ∉ ([] : List Nat)) rfl h with
      ⟨bad, _, _⟩ | ⟨_, _, tail⟩
    · exact (by decide : (1 : B256) ≠ 0) bad |>.elim
    · simpa only [mintConditionalLastWorld, ite_eq_left off] using mintReturn_inv fork mem tail.uncut
  · simp only [B256.eqCheck, ite_eq_right off] at h
    rcases ric_branchTo (g := t_137e_c12) (by decide : 12 ∉ ([] : List Nat)) rfl h with
      ⟨_, _, tail⟩ | ⟨bad, _, _⟩
    · obtain ⟨_, _, tail⟩ := mintKLast_inv fork tail
      simpa only [mintConditionalLastWorld, ite_eq_right off] using mintReturn_inv fork mem tail.uncut
    · exact (bad rfl).elim


/-- The complete133c forward suffix includes the actual conditional kLast charge and unlock cost. -/
theorem mintAfterUpdate_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G loadCost storeCost unlockCost : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1000)
    (loadCharge : f ≠ 0 → loadCost = sloadCost sevm b 8)
    (storeCharge : f ≠ 0 → storeCost = sstoreCost sevm (afterSload sevm b 8) 11
      (reserve0Read (b.getStorVal sevm.currentTarget 8) * reserve1Read (b.getStorVal sevm.currentTarget 8)))
    (kLastSentry : f ≠ 0 → gCallStipend < G + unlockCost + 1747 + storeCost)
    (unlockCharge : unlockCost = sstoreCost sevm
      ((mintConditionalLastWorld sevm b f).addLog (mintEventLog sevm amount0 amount1)) 12 1)
    (unlockSentry : gCallStipend < G + unlockCost + 31) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        M (G + unlockCost + 1747 + 20 + (if f = 0 then 0 else
          loadCost + storeCost + mul58Charge (reserve1Read (b.getStorVal sevm.currentTarget 8)) + 59)))
      t_133c_c11
      (.returned (St (mintReturnWorld sevm (mintConditionalLastWorld sevm b f) amount0 amount1)
        (liquidity :: R) (mintEventMemory M amount0 amount1) G)) := by
  have finish : SFunc.RunExact cert.prog sevm
      (St (mintConditionalLastWorld sevm b f)
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        M (G + unlockCost + 1747)) t_137e_c12
      (.returned (St (mintReturnWorld sevm (mintConditionalLastWorld sevm b f) amount0 amount1)
        (liquidity :: R) (mintEventMemory M amount0 amount1) G)) :=
    mintReturn_exact fork mem nonstatic (by omega : R.length ≤ 1007) unlockCharge unlockSentry
  unfold t_133c_c11
  by_cases off : f = 0
  · simp only [ite_eq_left off, Nat.add_zero]
    apply rx_dest
    apply rx_dup (w := f) rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by simp only [B256.eqCheck, ite_eq_left off])
      (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) (g := t_137e_c12) rfl
    simpa only [mintConditionalLastWorld, ite_eq_left off] using finish
  · simp only [ite_eq_right off]
    rw [show G + unlockCost + 1747 + 20 +
      (loadCost + storeCost + mul58Charge (reserve1Read (b.getStorVal sevm.currentTarget 8)) + 59) =
      (G + unlockCost + 1747 + loadCost + storeCost +
        mul58Charge (reserve1Read (b.getStorVal sevm.currentTarget 8)) + 59) + 20 from by omega]
    apply rx_dest
    apply rx_dup (w := f) rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (by simp only [B256.eqCheck, ite_eq_right off])
      (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    apply mintKLast_exact fork nonstatic room (loadCharge off) (storeCharge off) (kLastSentry off)
    simpa only [mintConditionalLastWorld, ite_eq_right off] using finish

/-- The actual update's two-word Sync buffer preserves the incoming192-byte pointer carrier. -/
theorem mintUpdateMemory_ptr {sevm : Sevm} {b : Devm} {M : Mem} {r0 r1 b0 b1 : B256}
    (mem : PtrMem 128 192 M) : PtrMem 128 192 (updateMemory sevm b M r0 r1 b0 b1) := by
  have a := mem.write 128 (reserve0Read (updateFinalPackedWord sevm b r0 r1 b0 b1)) (Or.inr (by decide))
  rw [show memExtSize 192 128 32 = 192 from by decide] at a
  have c := a.write 160 (reserve1Read (updateFinalPackedWord sevm b r0 r1 b0 b1)) (Or.inr (by decide))
  rw [show memExtSize 192 160 32 = 192 from by decide] at c
  exact c

/-- The actual LP post's complete memory includes both sequential scratch stages. -/
theorem mintLPPost_ptr {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord liquidity : B256} {G : Nat} (mem : PtrMem 128 192 M) :
    PtrMem 128 192 (lpMintPost sevm b R M toWord liquidity G).memory := by
  exact lpMintMemory_ptr (lpMintScratch_ptr mem toWord) toWord liquidity

/-- The actual1330 caller consumes update60 and all its true post-update continuation. -/
theorem mintUpdateCaller_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M G)
      t_1330_c11 o) :
    b0.toNat < 2 ^ 112 ∧ b1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧ ∃ gas,
      o = .returned (St
        (mintReturnWorld sevm (mintConditionalLastWorld sevm (updateWorld sevm b r0 r1 b0 b1) f) amount0 amount1)
        (liquidity :: R) (mintEventMemory (updateMemory sevm b M r0 r1 b0 b1) amount0 amount1) gas) := by
  have h := run.cut
  unfold t_1330_c11 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := b0) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := b1) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, call⟩ := ric_call (g := t_22e0_c60) rfl h
  rcases call with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨bound0, bound1, mutable, _, eq⟩ := update_inv fork mem callee
    cases eq
    obtain ⟨_, gas, result⟩ := mintAfterUpdate_inv fork (mintUpdateMemory_ptr mem) tail.uncut
    exact ⟨bound0, bound1, mutable, gas, result⟩
  · obtain ⟨_, _, _, _, eq⟩ := update_inv fork mem callee
    cases eq

/-- Literal LP world separates its completed sequential stores/log from the overwritten machine. -/
def mintLPWorld (sevm : Sevm) (b : Devm) (toWord value : B256) : Devm :=
  lpMintCreditBase sevm
    (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b + value))
      (transferBalanceSlot toWord.toAdr))
    toWord value (lpMintRecipientWord sevm (afterSload sevm b 0) toWord (lpMintSupplyWord sevm b + value) + value)

/-- The LP post carries BOTH actual scratch-write stages, then its Transfer log word. -/
def mintLPBuffer (M : Mem) (toWord value : B256) : Mem :=
  lpMintMemory ((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes) toWord value

theorem mintLPPost_image {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord value : B256} {G : Nat} :
    lpMintPost sevm b R M toWord value G = St (mintLPWorld sevm b toWord value) R (mintLPBuffer M toWord value) G := rfl

/-- Full priced post retains the actual recipient LP world and both scratch stages. -/
def mintPricedPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256) (residual gas : Nat) : Devm :=
  let post := lpMintPost sevm b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
    liquidity :: toWord :: ρ :: R) M toWord liquidity residual
  St (mintReturnWorld sevm (mintConditionalLastWorld sevm
    (updateWorld sevm post r0 r1 b0 b1) f) amount0 amount1)
    (liquidity :: R)
    (mintEventMemory (updateMemory sevm post post.memory r0 r1 b0 b1) amount0 amount1) gas


private theorem mintUpdateOracleActive_setMach {sevm : Sevm} {base : Devm} {mach : Mach} {old0 old1 : B256} :
    updateOracleActive sevm (base.setMach mach) old0 old1 ↔ updateOracleActive sevm base old0 old1 := by
  simp only [updateOracleActive, Devm.getStorVal_setMach]

private theorem mintUpdateOracleWorld_setMach {sevm : Sevm} {base : Devm} {mach : Mach} {old0 old1 : B256} :
    updateOracleWorld sevm (base.setMach mach) old0 old1 = (updateOracleWorld sevm base old0 old1).setMach mach := by
  unfold updateOracleWorld
  simp only [Devm.getStorVal_setMach, mintUpdateOracleActive_setMach]
  by_cases active : updateOracleActive sevm base old0 old1
  · simp only [ite_eq_left active, updateAccumulatorPost, afterSload_setMach,
      afterSstore_setMach, Devm.getStorVal_setMach]
  · simp only [ite_eq_right active, afterSload_setMach]

private theorem mintUpdateFinalPacked_setMach {sevm : Sevm} {base : Devm} {mach : Mach}
    {old0 old1 balance0 balance1 : B256} :
    updateFinalPackedWord sevm (base.setMach mach) old0 old1 balance0 balance1 =
      updateFinalPackedWord sevm base old0 old1 balance0 balance1 := by
  simp only [updateFinalPackedWord, mintUpdateOracleWorld_setMach, Devm.getStorVal_setMach]

private theorem mintUpdateWorld_setMach {sevm : Sevm} {base : Devm} {mach : Mach}
    {old0 old1 balance0 balance1 : B256} :
    updateWorld sevm (base.setMach mach) old0 old1 balance0 balance1 =
      (updateWorld sevm base old0 old1 balance0 balance1).setMach mach := by
  simp only [updateWorld, updateSyncPost, updatePackedPost, mintUpdateOracleWorld_setMach,
    mintUpdateFinalPacked_setMach, Devm.getStorVal_setMach, afterSload_setMach,
    afterSstore_setMach, addLog_setMach]

private theorem mintConditionalLastWorld_setMach {sevm : Sevm} {base : Devm} {mach : Mach} {f : B256} :
    mintConditionalLastWorld sevm (base.setMach mach) f = (mintConditionalLastWorld sevm base f).setMach mach := by
  unfold mintConditionalLastWorld
  by_cases off : f = 0
  · simp only [ite_eq_left off]
  · simp only [ite_eq_right off, mintKLastWorld, Devm.getStorVal_setMach,
      afterSload_setMach, afterSstore_setMach]

private theorem mintReturnWorld_setMach {sevm : Sevm} {base : Devm} {mach : Mach} {amount0 amount1 : B256} :
    mintReturnWorld sevm (base.setMach mach) amount0 amount1 = (mintReturnWorld sevm base amount0 amount1).setMach mach := by
  simp only [mintReturnWorld, addLog_setMach, afterSstore_setMach]

private theorem mintUpdateSyncPost_stateGas {sevm : Sevm} {base : Devm} {packed : B256} :
    (updateSyncPost sevm base packed).stateGas = base.stateGas := rfl

private theorem mintUpdateWorld_stateGas {sevm : Sevm} {base : Devm} {old0 old1 balance0 balance1 : B256} :
    (updateWorld sevm base old0 old1 balance0 balance1).stateGas = base.stateGas := by
  unfold updateWorld
  rw [mintUpdateSyncPost_stateGas]
  simp only [updatePackedPost, afterSstore_stateGas, afterSload_stateGas]
  unfold updateOracleWorld
  split <;> simp only [updateAccumulatorPost, afterSstore_stateGas, afterSload_stateGas]

private theorem mintConditionalLastWorld_stateGas {sevm : Sevm} {base : Devm} {f : B256} :
    (mintConditionalLastWorld sevm base f).stateGas = base.stateGas := by
  unfold mintConditionalLastWorld
  split <;> simp only [mintKLastWorld, afterSstore_stateGas, afterSload_stateGas]

private theorem mintReturnWorld_stateGas {sevm : Sevm} {base : Devm} {amount0 amount1 : B256} :
    (mintReturnWorld sevm base amount0 amount1).stateGas = base.stateGas := by
  unfold mintReturnWorld
  rw [afterSstore_stateGas]
  rfl

/-- The completed priced post depends on the literal LP world/buffer, not on overwritten cached machine fields. -/
theorem mintPricedPost_image {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {residual gas : Nat} :
    mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ residual gas =
      St (mintReturnWorld sevm (mintConditionalLastWorld sevm
        (updateWorld sevm (mintLPWorld sevm b toWord liquidity) r0 r1 b0 b1) f) amount0 amount1)
        (liquidity :: R)
        (mintEventMemory (updateMemory sevm (mintLPWorld sevm b toWord liquidity)
          (mintLPBuffer M toWord liquidity) r0 r1 b0 b1) amount0 amount1) gas := by
  unfold mintPricedPost
  rw [mintLPPost_image]
  generalize mintLPWorld sevm b toWord liquidity = base
  generalize mintLPBuffer M toWord liquidity = buffer
  simp only [St, mintUpdateWorld_setMach, mintConditionalLastWorld_setMach, mintReturnWorld_setMach,
    updateMemory, mintUpdateFinalPacked_setMach, Devm.memory_setMach, Devm.stateGas_setMach, Devm.setMach_setMach,
    mintReturnWorld_stateGas, mintConditionalLastWorld_stateGas, mintUpdateWorld_stateGas]

/-- Observations derived from the real common mint suffix, including its exact raw post. -/
def MintPricedResult (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256) (o : Outcome) : Prop :=
  0 < liquidity.toNat ∧ lpMintAccepts sevm b toWord liquidity ∧
    b0.toNat < 2 ^ 112 ∧ b1.toNat < 2 ^ 112 ∧ ∃ mintGas residual gas,
    SFunc.Run cert.prog sevm
      (St b (liquidity :: toWord :: 0x1330 :: supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        liquidity :: toWord :: ρ :: R) M mintGas) t_28ca_c62
      (.returned (lpMintPost sevm b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        liquidity :: toWord :: ρ :: R) M toWord liquidity residual)) ∧
    o = .returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ residual gas)


/-- Primitive affordability for the literal133c suffix; no successful continuation is a field. -/
structure MintAfterUpdateEnv (sevm : Sevm) (b : Devm) (f amount0 amount1 : B256) (G : Nat) where
  loadCost : Nat
  storeCost : Nat
  unlockCost : Nat
  loadCharge : f ≠ 0 → loadCost = sloadCost sevm b 8
  storeCharge : f ≠ 0 → storeCost = sstoreCost sevm (afterSload sevm b 8) 11
    (reserve0Read (b.getStorVal sevm.currentTarget 8) * reserve1Read (b.getStorVal sevm.currentTarget 8))
  kLastSentry : f ≠ 0 → gCallStipend < G + unlockCost + 1747 + storeCost
  unlockCharge : unlockCost = sstoreCost sevm
    ((mintConditionalLastWorld sevm b f).addLog (mintEventLog sevm amount0 amount1)) 12 1
  unlockSentry : gCallStipend < G + unlockCost + 31
  gas : Nat
  gas_eq : gas = G + unlockCost + 1747 + 20 + (if f = 0 then 0 else
    loadCost + storeCost + mul58Charge (reserve1Read (b.getStorVal sevm.currentTarget 8)) + 59)

/-- Actual update60 selected storage charges and its three genuine store sentries. -/
structure MintUpdateEnv (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) (G : Nat) where
  headerLoad : Nat
  load9 : Nat
  store9 : Nat
  load10 : Nat
  store10 : Nat
  load8 : Nat
  store8 : Nat
  headerCharge : headerLoad = sloadCost sevm b 8
  packedLoadCharge : load8 = sloadCost sevm (updateOracleWorld sevm b old0 old1) 8
  packedStoreCharge : store8 = sstoreCost sevm
    (afterSload sevm (updateOracleWorld sevm b old0 old1) 8) 8
    (updateFinalPackedWord sevm b old0 old1 balance0 balance1)
  oracleCharges : updateOracleActive sevm b old0 old1 →
    load9 = sloadCost sevm (afterSload sevm b 8) 9 ∧
    store9 = sstoreCost sevm (afterSload sevm (afterSload sevm b 8) 9) 9
      (updateAccumulatorWord ((afterSload sevm b 8).getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1)
        (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) ∧
    load10 = sloadCost sevm
      (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
        (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10 ∧
    store10 = sstoreCost sevm (afterSload sevm
      (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
        (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10) 10
      (updateAccumulatorWord
        ((updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)).getStorVal
          sevm.currentTarget 10) (updatePriceWord old1 old0)
        (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time))
  sentry8 : gCallStipend < G + updateSyncGas 192 + store8
  sentry10 : updateOracleActive sevm b old0 old1 →
    gCallStipend < G + updateSyncGas 192 + load8 + store8 + 110 + store10
  sentry9 : updateOracleActive sevm b old0 old1 →
    gCallStipend < G + updateSyncGas 192 + load8 + store8 + 110 + load10 + store10 + 42 + 149 + store9
  gas : Nat
  gas_eq : gas = G + updateSyncGas 192 + load8 + store8 + 110 +
    (if updateOracleActive sevm b old0 old1 then load9 + store9 + load10 + store10 + 382 else 0) +
    17 + 20 + (if updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0 = 0 then 0 else 17) +
    headerLoad + 75 +
    (if updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0 then 0 else 17) + 60

/-- Construct the actual1330 update caller, then the complete conditional kLast/log/unlock return. -/
theorem mintUpdateCaller_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (nonstatic : sevm.isStatic = false) (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112)
    (room : R.length ≤ 997)
    (finish : MintAfterUpdateEnv sevm (updateWorld sevm b r0 r1 b0 b1) f amount0 amount1 G)
    (charges : MintUpdateEnv sevm b r0 r1 b0 b1 finish.gas) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        M (charges.gas + 27)) t_1330_c11
      (.returned (St (mintReturnWorld sevm (mintConditionalLastWorld sevm (updateWorld sevm b r0 r1 b0 b1) f)
          amount0 amount1) (liquidity :: R)
        (mintEventMemory (updateMemory sevm b M r0 r1 b0 b1) amount0 amount1) G)) := by
  have tail : SFunc.RunExact cert.prog sevm
      (St (updateWorld sevm b r0 r1 b0 b1)
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        (updateMemory sevm b M r0 r1 b0 b1) finish.gas) t_133c_c11
      (.returned (St (mintReturnWorld sevm (mintConditionalLastWorld sevm (updateWorld sevm b r0 r1 b0 b1) f)
          amount0 amount1) (liquidity :: R)
        (mintEventMemory (updateMemory sevm b M r0 r1 b0 b1) amount0 amount1) G)) := by
    rw [finish.gas_eq]
    exact mintAfterUpdate_exact fork (mintUpdateMemory_ptr mem) nonstatic (by omega)
      finish.loadCharge finish.storeCharge finish.kLastSentry finish.unlockCharge finish.unlockSentry
  have callee : SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: b1 :: b0 :: 0x133c :: supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        liquidity :: toWord :: ρ :: R) M charges.gas) t_22e0_c60
      (.returned (St (updateWorld sevm b r0 r1 b0 b1)
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        (updateMemory sevm b M r0 r1 b0 b1) finish.gas)) := by
    rw [charges.gas_eq]
    exact update_exact fork mem nonstatic bound0 bound1 (by simp only [List.length_cons]; omega)
      charges.headerCharge charges.packedLoadCharge charges.packedStoreCharge charges.oracleCharges
      charges.sentry8 charges.sentry10 charges.sentry9
  unfold t_1330_c11
  apply rx_dest
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b1) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_22e0_c60) rfl callee tail

/-- Complete common priced mint: derive positive liquidity, the real recipient mint62, update60 and137e return. -/
theorem mintPriced_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) M G)
      t_12cd_c11 o) :
    MintPricedResult sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ o := by
  unfold MintPricedResult mintPricedPost
  have h := run.cut
  unfold t_12cd_c11 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := liquidity) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_gt hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨positive, _, h⟩
  · exact (bad.false_of_noOk (by decide : t_12d6_c11.noOk = true)).elim
  · have gt : (0 : B256) < liquidity := by
      by_contra neg
      simp only [B256.gtCheck, ite_eq_right neg] at positive
      exact positive rfl
    have natPositive : 0 < liquidity.toNat := by
      simpa only [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero] using gt
    obtain ⟨mintGas, residual, callee, accepted, tail⟩ :=
      lpMint_recipient_caller_inv (fun h => h) fork mem h
    let post := lpMintPost sevm b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
      liquidity :: toWord :: ρ :: R) M toWord liquidity residual
    have canonical : post = St post
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        post.memory residual := St.self rfl rfl
    change SFunc.RunCut cert.prog sevm [] post t_1330_c11 (.done o) at tail
    rw [canonical] at tail
    obtain ⟨bound0, bound1, _, gas, result⟩ :=
      mintUpdateCaller_inv fork (mintLPPost_ptr mem) tail.uncut
    exact ⟨natPositive, accepted, bound0, bound1, mintGas, residual, gas, callee, result⟩


/-- Construct the complete common priced mint from real LP guards and primitive store affordability. -/
theorem mintPriced_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (positive : 0 < liquidity.toNat) (accepted : lpMintAccepts sevm b toWord liquidity)
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) (room : R.length ≤ 997)
    (finish : MintAfterUpdateEnv sevm
      (updateWorld sevm (mintLPWorld sevm b toWord liquidity) r0 r1 b0 b1) f amount0 amount1 G)
    (charges : MintUpdateEnv sevm (mintLPWorld sevm b toWord liquidity) r0 r1 b0 b1 finish.gas)
    (supplySentry : lpMintSupplySentry sevm b toWord liquidity (charges.gas + 27))
    (creditSentry : lpMintCreditSentry sevm b toWord liquidity (charges.gas + 27)) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        M (lpMintGas sevm b toWord liquidity (charges.gas + 27) + 44)) t_12cd_c11
      (.returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ
        (charges.gas + 27) G)) := by
  let cache := supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R
  have tail : SFunc.RunExact cert.prog sevm
      (lpMintPost sevm b cache M toWord liquidity (charges.gas + 27)) t_1330_c11
      (.returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ
        (charges.gas + 27) G)) := by
    rw [mintLPPost_image, mintPricedPost_image]
    exact mintUpdateCaller_exact fork (lpMintMemory_ptr (lpMintScratch_ptr mem toWord) toWord liquidity)
      accepted.2.1 bound0 bound1 room finish charges
  have callee : SFunc.RunExact cert.prog sevm
      (St b (liquidity :: toWord :: 0x1330 :: cache)
        M (lpMintGas sevm b toWord liquidity (charges.gas + 27))) t_28ca_c62
      (.returned (lpMintPost sevm b cache M toWord liquidity (charges.gas + 27))) :=
    lpMint62_exact fork mem rfl rfl rfl rfl supplySentry creditSentry accepted.2.1
      accepted.1 accepted.2.2 (by dsimp only [cache]; simp only [List.length_cons]; omega)
  unfold t_12cd_c11
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := liquidity) rfl (by simp only [List.length_cons]; omega)
  apply rx_gt (v := 1) (by
    apply ite_eq_left
    change (0 : B256) < liquidity
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    exact positive) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_1326_c11
  apply rx_dest
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := toWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := liquidity) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_28ca_c62) rfl callee tail


def mintInitialLiquidity (amount0 amount1 : B256) : B256 := (Nat.sqrt (amount0 * amount1).toNat).toB256 - 1000

def mintInitialMinimumResidual (sevm : Sevm) (b : Devm) (toWord amount0 amount1 : B256) (recipientResidual : Nat) : Nat :=
  lpMintGas sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1) recipientResidual + 56

/-- The initial pricing arm constructs minimum0/1000, recipient LP and the complete update/log/unlock return. -/
theorem mintInitial_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (product : B256.Nofm amount0 amount1)
    (cover : (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256)
    (positive : 0 < (mintInitialLiquidity amount0 amount1).toNat)
    (minimum : lpMintAccepts sevm b 0 1000)
    (recipient : lpMintAccepts sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1))
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) (room : R.length ≤ 997)
    (finish : MintAfterUpdateEnv sevm
      (updateWorld sevm (mintLPWorld sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1))
        r0 r1 b0 b1) f amount0 amount1 G)
    (charges : MintUpdateEnv sevm
      (mintLPWorld sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1)) r0 r1 b0 b1 finish.gas)
    (supplySentry : lpMintSupplySentry sevm (mintLPWorld sevm b 0 1000) toWord
      (mintInitialLiquidity amount0 amount1) (charges.gas + 27))
    (creditSentry : lpMintCreditSentry sevm (mintLPWorld sevm b 0 1000) toWord
      (mintInitialLiquidity amount0 amount1) (charges.gas + 27))
    (minimumSupplySentry : lpMintSupplySentry sevm b 0 1000
      (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27)))
    (minimumCreditSentry : lpMintCreditSentry sevm b 0 1000
      (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27))) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (lpMintGas sevm b 0 1000
          (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27)) + 26 + 122 +
          sqrtCharge (amount0 * amount1).toNat + mul58Charge amount1)) t_123f_c41
      (.returned (mintPricedPost sevm (mintLPWorld sevm b 0 1000) R (mintLPBuffer M 0 1000)
        supply f amount1 amount0 b1 b0 r1 r0 (mintInitialLiquidity amount0 amount1) toWord ρ (charges.gas + 27) G)) := by
  let liquidity := mintInitialLiquidity amount0 amount1
  let cache := supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R
  let residual := mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27)
  let outcome := Outcome.returned (mintPricedPost sevm (mintLPWorld sevm b 0 1000) R (mintLPBuffer M 0 1000)
    supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ (charges.gas + 27) G)
  have tail : SFunc.RunExact cert.prog sevm (lpMintPost sevm b cache M 0 1000 residual) t_126b_c41 outcome := by
    rw [mintLPPost_image]
    unfold t_126b_c41
    have residualEq : residual =
        (lpMintGas sevm (mintLPWorld sevm b 0 1000) toWord liquidity (charges.gas + 27) + 44) + 12 := by
      dsimp only [residual, mintInitialMinimumResidual, liquidity]
    rw [residualEq]
    apply rx_dest
    apply rx_push rfl (by dsimp only [cache]; simp only [List.length_cons]; omega)
    apply rx_jump rfl
    exact mintPriced_exact fork (lpMintMemory_ptr (lpMintScratch_ptr mem 0) 0 1000)
      positive recipient bound0 bound1 room finish charges supplySentry creditSentry
  have callee : SFunc.RunExact cert.prog sevm (St b (1000 :: 0 :: 0x126b :: cache)
      M (lpMintGas sevm b 0 1000 residual)) t_28ca_c62
      (.returned (lpMintPost sevm b cache M 0 1000 residual)) :=
    lpMint62_exact (G := residual) (sourceCost := lpMintSourceCharge sevm b)
      (supplyCost := lpMintSupplyCharge sevm b 1000) (loadCost := lpMintRecipientLoadCharge sevm b 0 1000)
      (creditCost := lpMintCreditCharge sevm b 0 1000) fork mem rfl rfl rfl rfl
      minimumSupplySentry minimumCreditSentry minimum.2.1 minimum.1 minimum.2.2 (by dsimp only [cache]; simp only [List.length_cons]; omega)
  have minimumRun : SFunc.RunExact cert.prog sevm
      (St b (liquidity :: supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (lpMintGas sevm b 0 1000 residual + 26)) t_125c_c41 outcome := by
    unfold t_125c_c41
    apply rx_dest
    apply rx_swap (S' := oldLiquidity :: supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R) rfl
    apply rx_pop
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
    apply rx_push (w := 1000) rfl (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    exact rx_callRet (g := t_28ca_c62) rfl callee tail
  exact SFunc.runExact_iff_runExactCut_nil.mpr
    (mintInitialPrice_exact product cover (by omega) (SFunc.runExact_iff_runExactCut_nil.mp minimumRun))

/-- Complete later pricing constructs both checked products, floors/min70, recipient LP and full return. -/
theorem mintLater_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (product0 : B256.Nofm amount0 supply) (product1 : B256.Nofm amount1 supply)
    (nonzero0 : r0 ≠ 0) (nonzero1 : r1 ≠ 0)
    (positive : 0 < (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)).toNat)
    (recipient : lpMintAccepts sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)))
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) (room : R.length ≤ 997)
    (finish : MintAfterUpdateEnv sevm
      (updateWorld sevm (mintLPWorld sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)))
        r0 r1 b0 b1) f amount0 amount1 G)
    (charges : MintUpdateEnv sevm
      (mintLPWorld sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0))) r0 r1 b0 b1 finish.gas)
    (supplySentry : lpMintSupplySentry sevm b toWord
      (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27))
    (creditSentry : lpMintCreditSentry sevm b toWord
      (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27)) :
    SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (lpMintGas sevm b toWord
          (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27) + 44 + 137 +
          mul58Charge supply + mul58Charge supply + mintMin70Gas ((amount1 * supply) / r1) ((amount0 * supply) / r0)))
      t_1270_c41
      (.returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0
        (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) toWord ρ (charges.gas + 27) G)) := by
  have body : SFunc.RunExact cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0) :: toWord :: ρ :: R)
        M (lpMintGas sevm b toWord
          (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27) + 44)) t_12cd_c11
      (.returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0
        (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) toWord ρ (charges.gas + 27) G)) :=
    mintPriced_exact fork mem positive recipient bound0 bound1 room finish charges supplySentry creditSentry
  exact SFunc.runExact_iff_runExactCut_nil.mpr (mintLaterPrice_exact (oldLiquidity := oldLiquidity)
    oldBound0 oldBound1 product0 product1 nonzero0 nonzero1 (by omega) (SFunc.runExact_iff_runExactCut_nil.mp body))

/-- The initial arm consumes the zero-address minimum LP mint before the complete common suffix. -/
def MintInitialResult (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (supply f amount1 amount0 b1 b0 r1 r0 toWord ρ : B256) (o : Outcome) : Prop :=
  B256.Nofm amount0 amount1 ∧ (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256 ∧
  ∃ minimumGas residual,
    let liquidity := (Nat.sqrt (amount0 * amount1).toNat).toB256 - 1000
    let cache := supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R
    let post := lpMintPost sevm b cache M 0 1000 residual
    SFunc.Run cert.prog sevm (St b (1000 :: 0 :: 0x126b :: cache) M minimumGas) t_28ca_c62
      (.returned post) ∧ lpMintAccepts sevm b 0 1000 ∧
    MintPricedResult sevm post R post.memory supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ o

theorem mintInitial_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_123f_c41 o) :
    MintInitialResult sevm b R M supply f amount1 amount0 b1 b0 r1 r0 toWord ρ o := by
  unfold MintInitialResult
  obtain ⟨product, cover, _, price⟩ := mintInitialPrice_inv run.cut
  obtain ⟨minimumGas, residual, callee, accepted, tail⟩ :=
    lpMint_minimum_caller_inv (fun h => h) fork mem price
  let liquidity := (Nat.sqrt (amount0 * amount1).toNat).toB256 - 1000
  let cache := supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R
  let post := lpMintPost sevm b cache M 0 1000 residual
  have canonical : post = St post cache post.memory residual := St.self rfl rfl
  change SFunc.RunCut cert.prog sevm [] post t_126b_c41 (.done o) at tail
  rw [canonical] at tail
  unfold t_126b_c41 at tail
  obtain ⟨_, tail⟩ := ric_dest tail
  obtain ⟨_, hs, tail⟩ := ric_next tail; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, tail⟩ := ric_jump (g := t_12cd_c11) (by decide : 11 ∉ ([] : List Nat)) rfl tail
  have result := mintPriced_inv fork (mintLPPost_ptr mem) tail.uncut
  exact ⟨product, cover, minimumGas, residual, callee, accepted, result⟩

/-- The later arm consumes both floor quotients and literal min70 in the complete common suffix. -/
def MintLaterResult (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (supply f amount1 amount0 b1 b0 r1 r0 toWord ρ : B256) (o : Outcome) : Prop :=
  B256.Nofm amount0 supply ∧ r0 ≠ 0 ∧ B256.Nofm amount1 supply ∧ r1 ≠ 0 ∧
    MintPricedResult sevm b R M supply f amount1 amount0 b1 b0 r1 r0
      (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) toWord ρ o

theorem mintLater_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {supply f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_1270_c41 o) :
    MintLaterResult sevm b R M supply f amount1 amount0 b1 b0 r1 r0 toWord ρ o := by
  unfold MintLaterResult
  obtain ⟨product0, nonzero0, product1, nonzero1, _, tail⟩ := mintLaterPrice_inv bound0 bound1 run.cut
  exact ⟨product0, nonzero0, product1, nonzero1, mintPriced_inv fork mem tail.uncut⟩

/-- The complete actual1233 suffix selects its pricing arm from the current slot0 read. -/
def MintAfterFeeResult (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (f amount1 amount0 b1 b0 r1 r0 toWord ρ : B256) (o : Outcome) : Prop :=
  let supply := lpMintSupplyWord sevm b
  let loaded := afterSload sevm b 0
  if supply = 0 then
    MintInitialResult sevm loaded R M supply f amount1 amount0 b1 b0 r1 r0 toWord ρ o
  else
    MintLaterResult sevm loaded R M supply f amount1 amount0 b1 b0 r1 r0 toWord ρ o

/-- Successful post-fee mint derives BOTH supply-arm observations and the complete raw return. -/
theorem mintAfterFee_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_1233_c41 o) :
    MintAfterFeeResult sevm b R M f amount1 amount0 b1 b0 r1 r0 toWord ρ o := by
  have h := run.cut
  unfold t_1233_c41 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := f :: lpMintSupplyWord sevm b :: 0 :: amount1 :: amount0 ::
    b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := 0 :: lpMintSupplyWord sevm b :: f :: amount1 :: amount0 ::
    b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := lpMintSupplyWord sevm b) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branch h with ⟨zero, _, tail⟩ | ⟨nonzero, _, tail⟩
  · simpa only [MintAfterFeeResult, ite_eq_left zero] using mintInitial_inv fork mem tail.uncut
  · simpa only [MintAfterFeeResult, ite_eq_right nonzero] using mintLater_inv fork mem bound0 bound1 tail.uncut

/-- The actual1233 prefix reads the current supply and selects its literal pricing tree. -/
theorem mintAfterFeePrefix_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 997)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 0)
        (lpMintSupplyWord sevm b :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M G) (if lpMintSupplyWord sevm b = 0 then t_123f_c41 else t_1270_c41) o) :
    SFunc.RunExact cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (G + sloadCost sevm b 0 + 28)) t_1233_c41 o := by
  unfold t_1233_c41
  rw [show G + sloadCost sevm b 0 + 28 = ((G + 24) + sloadCost sevm b 0) + 4 from by omega]
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (S' := f :: lpMintSupplyWord sevm b :: 0 :: amount1 :: amount0 :: b1 :: b0 ::
    r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) rfl
  apply rx_swap (S' := 0 :: lpMintSupplyWord sevm b :: f :: amount1 :: amount0 :: b1 :: b0 ::
    r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) rfl
  apply rx_pop
  apply rx_dup (w := lpMintSupplyWord sevm b) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  by_cases zero : lpMintSupplyWord sevm b = 0
  · rw [zero]
    apply rx_branch_zero
    simpa only [zero, ite_true] using body
  · apply rx_branch_succ zero
    simpa only [ite_eq_right zero] using body

/-- Initial-arm real guard and affordability data, without an assumed successful suffix. -/
structure MintInitialEnv (sevm : Sevm) (b : Devm) (f toWord amount0 amount1 b0 b1 r0 r1 : B256) (G : Nat) where
  product : B256.Nofm amount0 amount1
  cover : (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256
  positive : 0 < (mintInitialLiquidity amount0 amount1).toNat
  minimum : lpMintAccepts sevm b 0 1000
  recipient : lpMintAccepts sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1)
  finish : MintAfterUpdateEnv sevm
    (updateWorld sevm (mintLPWorld sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1))
      r0 r1 b0 b1) f amount0 amount1 G
  charges : MintUpdateEnv sevm
    (mintLPWorld sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1)) r0 r1 b0 b1 finish.gas
  supplySentry : lpMintSupplySentry sevm (mintLPWorld sevm b 0 1000) toWord
    (mintInitialLiquidity amount0 amount1) (charges.gas + 27)
  creditSentry : lpMintCreditSentry sevm (mintLPWorld sevm b 0 1000) toWord
    (mintInitialLiquidity amount0 amount1) (charges.gas + 27)
  minimumSupplySentry : lpMintSupplySentry sevm b 0 1000
    (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27))
  minimumCreditSentry : lpMintCreditSentry sevm b 0 1000
    (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27))

/-- Later-arm real checked arithmetic, recipient and primitive affordability data. -/
structure MintLaterEnv (sevm : Sevm) (b : Devm) (supply f toWord amount0 amount1 b0 b1 r0 r1 : B256) (G : Nat) where
  product0 : B256.Nofm amount0 supply
  product1 : B256.Nofm amount1 supply
  nonzero0 : r0 ≠ 0
  nonzero1 : r1 ≠ 0
  positive : 0 < (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)).toNat
  recipient : lpMintAccepts sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0))
  finish : MintAfterUpdateEnv sevm
    (updateWorld sevm (mintLPWorld sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)))
      r0 r1 b0 b1) f amount0 amount1 G
  charges : MintUpdateEnv sevm
    (mintLPWorld sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0))) r0 r1 b0 b1 finish.gas
  supplySentry : lpMintSupplySentry sevm b toWord
    (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27)
  creditSentry : lpMintCreditSentry sevm b toWord
    (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27)

def MintInitialEnv.gas {sevm : Sevm} {b : Devm} {f toWord amount0 amount1 b0 b1 r0 r1 : B256} {G : Nat}
    (env : MintInitialEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) : Nat :=
  lpMintGas sevm b 0 1000 (mintInitialMinimumResidual sevm b toWord amount0 amount1 (env.charges.gas + 27)) +
    26 + 122 + sqrtCharge (amount0 * amount1).toNat + mul58Charge amount1

def MintLaterEnv.gas {sevm : Sevm} {b : Devm} {supply f toWord amount0 amount1 b0 b1 r0 r1 : B256} {G : Nat}
    (env : MintLaterEnv sevm b supply f toWord amount0 amount1 b0 b1 r0 r1 G) : Nat :=
  lpMintGas sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (env.charges.gas + 27) +
    44 + 137 + mul58Charge supply + mul58Charge supply +
    mintMin70Gas ((amount1 * supply) / r1) ((amount0 * supply) / r0)

/-- Branch data are conditional on the actual slot0 value, not an externally selected arm. -/
structure MintAfterFeeEnv (sevm : Sevm) (b : Devm) (f toWord amount0 amount1 b0 b1 r0 r1 : B256) (G : Nat) where
  initial : lpMintSupplyWord sevm b = 0 →
    MintInitialEnv sevm (afterSload sevm b 0) f toWord amount0 amount1 b0 b1 r0 r1 G
  later : lpMintSupplyWord sevm b ≠ 0 →
    MintLaterEnv sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b) f toWord amount0 amount1 b0 b1 r0 r1 G

def MintAfterFeeEnv.armGas {sevm : Sevm} {b : Devm} {f toWord amount0 amount1 b0 b1 r0 r1 : B256} {G : Nat}
    (env : MintAfterFeeEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) : Nat :=
  if zero : lpMintSupplyWord sevm b = 0 then (env.initial zero).gas else (env.later zero).gas

def MintAfterFeeEnv.post {sevm : Sevm} {b : Devm} {f toWord amount0 amount1 b0 b1 r0 r1 : B256} {G : Nat}
    (env : MintAfterFeeEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) (M : Mem) (R : List B256) (ρ : B256) : Devm :=
  if zero : lpMintSupplyWord sevm b = 0 then
    mintPricedPost sevm (mintLPWorld sevm (afterSload sevm b 0) 0 1000) R (mintLPBuffer M 0 1000)
      (lpMintSupplyWord sevm b) f amount1 amount0 b1 b0 r1 r0 (mintInitialLiquidity amount0 amount1) toWord ρ
      ((env.initial zero).charges.gas + 27) G
  else
    mintPricedPost sevm (afterSload sevm b 0) R M (lpMintSupplyWord sevm b) f amount1 amount0 b1 b0 r1 r0
      (mintMinWord ((amount1 * lpMintSupplyWord sevm b) / r1) ((amount0 * lpMintSupplyWord sevm b) / r0)) toWord ρ
      ((env.later zero).charges.gas + 27) G

/-- Complete1233 exact forward derives its selected tree from the real supply SLOAD and builds BOTH full paths. -/
theorem mintAfterFee_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) (room : R.length ≤ 997)
    (env : MintAfterFeeEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) :
    SFunc.RunExact cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (env.armGas + sloadCost sevm b 0 + 28)) t_1233_c41 (.returned (env.post M R ρ)) := by
  apply mintAfterFeePrefix_exact fork room
  by_cases zero : lpMintSupplyWord sevm b = 0
  · simp only [ite_eq_left zero, MintAfterFeeEnv.armGas, MintAfterFeeEnv.post, dite_eq_left zero]
    let selected := env.initial zero
    exact mintInitial_exact fork mem selected.product selected.cover selected.positive selected.minimum
      selected.recipient bound0 bound1 room selected.finish selected.charges selected.supplySentry selected.creditSentry
      selected.minimumSupplySentry selected.minimumCreditSentry
  · simp only [ite_eq_right zero, MintAfterFeeEnv.armGas, MintAfterFeeEnv.post, dite_eq_right zero]
    let selected := env.later zero
    exact mintLater_exact fork mem oldBound0 oldBound1 selected.product0 selected.product1 selected.nonzero0
      selected.nonzero1 selected.positive selected.recipient bound0 bound1 room selected.finish selected.charges
      selected.supplySentry selected.creditSentry

end Blanc.Lift.UniswapV2Pair
