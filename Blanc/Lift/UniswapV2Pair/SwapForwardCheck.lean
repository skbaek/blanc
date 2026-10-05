import Blanc.Lift.UniswapV2Pair.SwapForwardUpdate
import Blanc.Lift.ExactWalkOps

/-! Forward (gas-exact) duals of the swap body's checked arithmetic: the SafeMath `K`
check (`t_0bd5_c8` .. `t_0c69_c8`, dual of `swapK_inv`) and the two amount-in ternaries with
the `INSUFFICIENT_INPUT_AMOUNT` guard (`t_0af5_c5` .. `t_0b80_c8`, dual of `swapInputs_inv`). -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- One straight-line forward step over a concrete stack (the swap back-half walks). -/
macro "swapfwd_rx" : tactic => `(tactic| first
  | apply rx_dest
  | apply rx_push rfl (by simp only [List.length_cons]; omega)
  | apply rx_dup rfl (by simp only [List.length_cons]; omega)
  | (apply rx_swap rfl; dsimp only [List.set])
  | apply rx_pop
  | apply rx_and rfl (by simp only [List.length_cons]; omega))

/-- A masked cached reserve fits 112 bits. -/
theorem swapMasked_lt (r : B256) : (reserveMask112 &&& r).toNat < 2 ^ 112 := by
  rw [B256.and_comm, show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
    PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
  exact Nat.mod_lt _ (by decide)

/-- The reserve product `K` is computed without wrapping. -/
theorem swapReserveProduct_nofm (r0 r1 : B256) :
    B256.Nofm (reserveMask112 &&& r0) (r1 &&& reserveMask112) ∧
    B256.Nofm ((reserveMask112 &&& r0) * (r1 &&& reserveMask112)) 1000000 := by
  have h0 := swapMasked_lt r0
  have h1 : (r1 &&& reserveMask112).toNat < 2 ^ 112 := by
    rw [B256.and_comm]
    exact swapMasked_lt r1
  have prod : (reserveMask112 &&& r0).toNat * (r1 &&& reserveMask112).toNat < 2 ^ 224 := by
    have := Nat.mul_lt_mul'' h0 h1
    rw [show 2 ^ 112 * 2 ^ 112 = 2 ^ 224 from by decide] at this
    exact this
  have first : B256.Nofm (reserveMask112 &&& r0) (r1 &&& reserveMask112) := by
    unfold B256.Nofm
    omega
  refine ⟨first, ?_⟩
  unfold B256.Nofm
  rw [B256.toNat_mul_eq_of_nofm first, show (1000000 : B256).toNat = 1000000 from by decide]
  omega

/-- The exact charge of the `K` check: four fixed-operand multiplications, two checked
subtractions, the reserve product and the adjusted product (`mul58Charge` keeps the literal
zero-multiplier shortcut), and the comparison. -/
def swapKCharge (bal1 in1 r1 : B256) : Nat :=
  20 + mul58Charge (bal1 * 1000 - in1 * 3) + 27 + mul58Charge 1000000 + 21 +
    mul58Charge (r1 &&& reserveMask112) + 53 + 54 + 21 + mul58Charge 1000 + 27 + mul58Charge 3 +
    38 + 54 + 21 + mul58Charge 1000 + 27 + mul58Charge 3 + 33

/-- **Forward SafeMath `K` check** (dual of `swapK_inv`): from the raw facts the successful
check exposes, the checked adjusted balances and the comparison reach the `_update` call. -/
theorem swapK_exact {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {in1 in0 bal1 bal0 r1 r0 : B256} (k : SwapKFacts bal0 bal1 in0 in1 r0 r1)
    (room : S.length ≤ 1000)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((bal1 * 1000 - in1 * 3) :: (bal0 * 1000 - in0 * 3) ::
        in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: S) M G) t_0cd6_c8 o) :
    SFunc.RunExact cert.prog sevm
      (St b (in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: S) M (G + swapKCharge bal1 in1 r1))
      t_0bd5_c8 o := by
  obtain ⟨resMul, kMul⟩ := swapReserveProduct_nofm r0 r1
  have notLt : B256.ltCheck ((bal0 * 1000 - in0 * 3) * (bal1 * 1000 - in1 * 3))
      ((reserveMask112 &&& r0) * (r1 &&& reserveMask112) * 1000000) = 0 := by
    unfold B256.ltCheck
    exact ite_eq_right k.k
  rw [show G + swapKCharge bal1 in1 r1 = G + 20 + mul58Charge (bal1 * 1000 - in1 * 3) + 27 +
    mul58Charge 1000000 + 21 + mul58Charge (r1 &&& reserveMask112) + 53 + 54 + 21 +
    mul58Charge 1000 + 27 + mul58Charge 3 + 38 + 54 + 21 + mul58Charge 1000 + 27 +
    mul58Charge 3 + 33 by unfold swapKCharge; omega]
  unfold t_0bd5_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact k.in0Mul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0beb_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact k.bal0Mul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0bfd_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (sub59_exact k.cover0 (by simp only [List.length_cons]; omega)) ?_
  unfold t_0c09_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact k.in1Mul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0beb_c8_1
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact k.bal1Mul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0bfd_c8_1
  repeat swapfwd_rx
  refine rx_callRet rfl (sub59_exact k.cover1 (by simp only [List.length_cons]; omega)) ?_
  unfold t_0c21_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact resMul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0c4d_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact kMul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0c59_c8
  repeat swapfwd_rx
  refine rx_callRet rfl (mul58_exact k.adjustedMul (by simp only [List.length_cons]; omega)) ?_
  unfold t_0c69_c8
  apply rx_dest
  apply rx_lt notLt (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  swapfwd_rx
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

/-- Gas of one amount-in ternary arm: the subtraction arm or the literal-zero jump. -/
def swapInArmGas (balance reserve amountOut : B256) : Nat :=
  if (reserveMask112 &&& reserve) - amountOut < balance then 22 else 14

/-- The exact charge of both ternaries and the input guard (the guard re-tests `in1` only
when `in0 = 0`). -/
def swapInputsCharge (bal0 bal1 r0 r1 a0 a1 : B256) : Nat :=
  14 + (if 0 < swapInWord bal0 r0 a0 then 0 else 11) + 31 + swapInArmGas bal1 r1 a1 + 43 +
    swapInArmGas bal0 r0 a0 + 58

theorem swapIn_gt_ne {balance reserve amountOut : B256}
    (h : (reserveMask112 &&& reserve) - amountOut < balance) :
    B256.gtCheck balance ((reserve &&& reserveMask112) - amountOut) = 1 := by
  rw [B256.and_comm]
  unfold B256.gtCheck
  exact ite_eq_left h

theorem swapIn_gt_eq {balance reserve amountOut : B256}
    (h : ¬ (reserveMask112 &&& reserve) - amountOut < balance) :
    B256.gtCheck balance ((reserve &&& reserveMask112) - amountOut) = 0 := by
  rw [B256.and_comm]
  unfold B256.gtCheck
  exact ite_eq_right h

/-- **Forward amount-in ternaries and input guard** (dual of `swapInputs_inv`): decode the
second balance word at `p`, infer both inputs, and pass `INSUFFICIENT_INPUT_AMOUNT`. -/
theorem swapInputs_exact {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G n : Nat}
    {rds p t1 t0 bal0 bal1 r1 r0 len off toW a1 a0 : B256} {o : Outcome}
    (mem : PtrMem p n M) (cover : p.toNat + 32 ≤ n)
    (word : Bytes.toB256 (M.read p.toNat 32).1 = bal1)
    (guard : 0 < swapInWord bal0 r0 a0 ∨ 0 < swapInWord bal1 r1 a1)
    (room : S.length ≤ 1000)
    (body : SFunc.RunExact cert.prog sevm
      (St b (swapInWord bal1 r1 a1 :: swapInWord bal0 r0 a0 :: bal1 :: bal0 :: r1 :: r0 ::
        len :: off :: toW :: a1 :: a0 :: S) M G) t_0bd5_c8 o) :
    SFunc.RunExact cert.prog sevm
      (St b (rds :: p :: t1 :: t0 :: 0 :: bal0 :: r1 :: r0 :: len :: off :: toW :: a1 :: a0 :: S) M
        (G + swapInputsCharge bal0 bal1 r0 r1 a0 a1)) t_0af5_c5 o := by
  unfold swapInputsCharge
  simp only [← Nat.add_assoc]
  unfold t_0af5_c5
  apply rx_dest
  apply rx_pop
  refine rx_mload (c := 3) ?_ word (mem.read_self cover) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 cover, Nat.sub_self]
    rfl
  repeat swapfwd_rx
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  have first : ∀ v, v = swapInWord bal0 r0 a0 → SFunc.RunExact cert.prog sevm
      (St b (v :: 0 :: bal1 :: bal0 :: r1 :: r0 ::
        len :: off :: toW :: a1 :: a0 :: S) M
        ((G + 14 + if 0 < swapInWord bal0 r0 a0 then 0 else 11) + 31 + swapInArmGas bal1 r1 a1 + 43))
      t_0b35_c6 o := by
    intro v hv
    subst hv
    have second : ∀ v, v = swapInWord bal1 r1 a1 → SFunc.RunExact cert.prog sevm
        (St b (v :: 0 :: swapInWord bal0 r0 a0 :: bal1 :: bal0 :: r1 :: r0 ::
          len :: off :: toW :: a1 :: a0 :: S) M
          ((G + 14 + if 0 < swapInWord bal0 r0 a0 then 0 else 11) + 31)) t_0b6f_c7 o := by
      intro v hv
      subst hv
      unfold t_0b6f_c7
      repeat swapfwd_rx
      by_cases pos0 : 0 < swapInWord bal0 r0 a0
      · rw [ite_eq_left pos0]
        apply rx_gt (v := 1) (ite_eq_left pos0) (by simp only [List.length_cons]; omega)
        repeat swapfwd_rx
        refine rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl ?_
        unfold t_0b80_c8
        repeat swapfwd_rx
        exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body
      · have pos1 : 0 < swapInWord bal1 r1 a1 := guard.resolve_left pos0
        rw [ite_eq_right pos0]
        apply rx_gt (v := 0) (ite_eq_right pos0) (by simp only [List.length_cons]; omega)
        repeat swapfwd_rx
        refine rx_branchTo_zero ?_
        unfold t_0b7b_c7
        repeat swapfwd_rx
        apply rx_gt (v := 1) (ite_eq_left pos1) (by simp only [List.length_cons]; omega)
        unfold t_0b80_c8
        repeat swapfwd_rx
        exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body
    unfold t_0b35_c6
    repeat swapfwd_rx
    apply rx_sub (by simp only [List.length_cons]; omega)
    apply rx_dup rfl (by simp only [List.length_cons]; omega)
    by_cases above : (reserveMask112 &&& r1) - a1 < bal1
    · rw [show swapInArmGas bal1 r1 a1 = 22 from ite_eq_left above]
      apply rx_gt (v := 1) (ite_eq_left above) (by simp only [List.length_cons]; omega)
      swapfwd_rx
      refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
      unfold t_0b59_c6
      repeat swapfwd_rx
      apply rx_sub (by simp only [List.length_cons]; omega)
      apply rx_dup rfl (by simp only [List.length_cons]; omega)
      apply rx_sub (by simp only [List.length_cons]; omega)
      have e : swapInWord bal1 r1 a1 = bal1 - ((reserveMask112 &&& r1) - a1) := ite_eq_left above
      exact second _ e.symm
    · rw [show swapInArmGas bal1 r1 a1 = 14 from ite_eq_right above]
      apply rx_gt (v := 0) (ite_eq_right above) (by simp only [List.length_cons]; omega)
      swapfwd_rx
      refine rx_branch_zero ?_
      unfold t_0b53_c6
      repeat swapfwd_rx
      refine rx_jump rfl ?_
      have e : swapInWord bal1 r1 a1 = 0 := ite_eq_right above
      exact second _ e.symm
  by_cases above : (reserveMask112 &&& r0) - a0 < bal0
  · rw [show swapInArmGas bal0 r0 a0 = 22 from ite_eq_left above]
    apply rx_gt (swapIn_gt_ne above) (by simp only [List.length_cons]; omega)
    swapfwd_rx
    refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
    unfold t_0b1f_c5
    repeat swapfwd_rx
    apply rx_sub (by simp only [List.length_cons]; omega)
    apply rx_dup rfl (by simp only [List.length_cons]; omega)
    apply rx_sub (by simp only [List.length_cons]; omega)
    have e : swapInWord bal0 r0 a0 = bal0 - ((reserveMask112 &&& r0) - a0) := ite_eq_left above
    exact first _ e.symm
  · rw [show swapInArmGas bal0 r0 a0 = 14 from ite_eq_right above]
    apply rx_gt (swapIn_gt_eq above) (by simp only [List.length_cons]; omega)
    swapfwd_rx
    refine rx_branch_zero ?_
    unfold t_0b19_c5
    repeat swapfwd_rx
    refine rx_jump rfl ?_
    have e : swapInWord bal0 r0 a0 = 0 := ite_eq_right above
    exact first _ e.symm

end Blanc.Lift.UniswapV2Pair
