import Blanc.Lift.UniswapV2Pair.SwapBalanceWalk
import Blanc.Lift.UniswapV2Pair.FeeMintArithmetic

/-! The actual swap body after both balance observations: the two amount-in
ternaries (`t_0af5_c5` .. `t_0b6f_c7`), the `INSUFFICIENT_INPUT_AMOUNT` guard
(`t_0b80_c8`) and the SafeMath `K` check (`t_0bd5_c8` .. `t_0c69_c8`), up to the
`_update` call at `t_0cd6_c8`. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem swap_gt_of_gtCheck_ne {x y : B256} (h : B256.gtCheck x y ≠ 0) : y < x := by
  unfold B256.gtCheck at h
  split at h
  · assumption
  · exact absurd rfl h

theorem swap_not_gt_of_gtCheck_eq {x y : B256} (h : B256.gtCheck x y = 0) : ¬ y < x := by
  unfold B256.gtCheck at h
  split at h
  · exact absurd h (by decide)
  · assumption

theorem swap_not_lt_of_ltCheck_eq {x y : B256} (h : B256.ltCheck x y = 0) : ¬ x < y := by
  unfold B256.ltCheck at h
  split at h
  · exact absurd h (by decide)
  · assumption

/-- One actual amount-in ternary over the masked cached reserve. -/
def swapInWord (balance reserve amountOut : B256) : B256 :=
  if (reserveMask112 &&& reserve) - amountOut < balance then
    balance - ((reserveMask112 &&& reserve) - amountOut) else 0

/-- Both ternaries and the input guard: the successful path reaches the checked
arithmetic with both inferred inputs, and at least one of them is nonzero. -/
theorem swapInputsDecoded_inv {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t1 t0 bal0 bal1 r1 r0 len off toW a1 a0 : B256} {seg : Seg}
    (run : SFunc.RunCut cert.prog sevm []
      (St b (bal1 :: t1 :: t0 :: 0 :: bal0 :: r1 :: r0 :: len :: off :: toW :: a1 :: a0 :: S) M G)
      (swapBalanceDecodedTail true) seg) :
    (0 < swapInWord bal0 r0 a0 ∨ 0 < swapInWord bal1 r1 a1) ∧ ∃ G',
      SFunc.RunCut cert.prog sevm []
        (St b (swapInWord bal1 r1 a1 :: swapInWord bal0 r0 a0 :: bal1 :: bal0 :: r1 :: r0 ::
          len :: off :: toW :: a1 :: a0 :: S) M G') t_0bd5_c8 seg := by
  dsimp only [swapBalanceDecodedTail, t_0af5_c5, ite_true] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rw [B256.and_comm] at run
  -- first ternary: both arms meet at `t_0b35_c6` with `in0` on top
  have first : ∃ G1, SFunc.RunCut cert.prog sevm []
      (St b (swapInWord bal0 r0 a0 :: 0 :: bal1 :: bal0 :: r1 :: r0 ::
        len :: off :: toW :: a1 :: a0 :: S) M G1) t_0b35_c6 seg := by
    rcases ric_branch run with ⟨zero, _, run⟩ | ⟨nonzero, _, run⟩
    · unfold t_0b19_c5 at run
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨G1, run⟩ := ric_jump (by decide) rfl run
      refine ⟨G1, ?_⟩
      unfold swapInWord
      rw [if_neg (show ¬ (reserveMask112 &&& r0) - a0 < bal0 from swap_not_gt_of_gtCheck_eq zero)]
      exact run
    · unfold t_0b1f_c5 at run
      obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sub hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨G1, hs, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_sub hs
      refine ⟨G1, ?_⟩
      unfold swapInWord
      rw [if_pos (show (reserveMask112 &&& r0) - a0 < bal0 from swap_gt_of_gtCheck_ne nonzero)]
      exact run
  clear run
  obtain ⟨_, run⟩ := first
  unfold t_0b35_c6 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  have second : ∃ G2, SFunc.RunCut cert.prog sevm []
      (St b (swapInWord bal1 r1 a1 :: 0 :: swapInWord bal0 r0 a0 :: bal1 :: bal0 :: r1 :: r0 ::
        len :: off :: toW :: a1 :: a0 :: S) M G2) t_0b6f_c7 seg := by
    rcases ric_branch run with ⟨zero, _, run⟩ | ⟨nonzero, _, run⟩
    · unfold t_0b53_c6 at run
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨G2, run⟩ := ric_jump (by decide) rfl run
      refine ⟨G2, ?_⟩
      unfold swapInWord
      rw [if_neg (show ¬ (reserveMask112 &&& r1) - a1 < bal1 from swap_not_gt_of_gtCheck_eq zero)]
      exact run
    · unfold t_0b59_c6 at run
      obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sub hs
      obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨G2, hs, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_sub hs
      refine ⟨G2, ?_⟩
      unfold swapInWord
      rw [if_pos (show (reserveMask112 &&& r1) - a1 < bal1 from swap_gt_of_gtCheck_ne nonzero)]
      exact run
  clear run
  obtain ⟨_, run⟩ := second
  unfold t_0b6f_c7 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branchTo (g := t_0b80_c8) (by decide) rfl run with ⟨zero, _, run⟩ | ⟨nonzero, _, run⟩
  · unfold t_0b7b_c7 at run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt hs
    unfold t_0b80_c8 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    rcases ric_branch run with ⟨_, _, failed⟩ | ⟨accepted, G', run⟩
    · exact (failed.false_of_noOk (by decide : t_0b85_c8.noOk = true)).elim
    · exact ⟨Or.inr (swap_gt_of_gtCheck_ne accepted), G', run⟩
  · unfold t_0b80_c8 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
    rcases ric_branch run with ⟨_, _, failed⟩ | ⟨_, G', run⟩
    · exact (failed.false_of_noOk (by decide : t_0b85_c8.noOk = true)).elim
    · exact ⟨Or.inl (swap_gt_of_gtCheck_ne nonzero), G', run⟩

/-- Both actual decoders, input ternaries and the successful input guard. -/
theorem swapInputs_inv {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {rds p t1 t0 bal0 bal1 r1 r0 len off toW a1 a0 : B256} {seg : Seg}
    (word : Bytes.toB256 (M.read p.toNat 32).1 = bal1) (self : (M.read p.toNat 32).2 = M)
    (run : SFunc.RunCut cert.prog sevm []
      (St b (rds :: p :: t1 :: t0 :: 0 :: bal0 :: r1 :: r0 :: len :: off :: toW :: a1 :: a0 :: S) M G)
      t_0af5_c5 seg) :
    (0 < swapInWord bal0 r0 a0 ∨ 0 < swapInWord bal1 r1 a1) ∧ ∃ G',
      SFunc.RunCut cert.prog sevm []
        (St b (swapInWord bal1 r1 a1 :: swapInWord bal0 r0 a0 :: bal1 :: bal0 :: r1 :: r0 ::
          len :: off :: toW :: a1 :: a0 :: S) M G') t_0bd5_c8 seg := by
  unfold t_0af5_c5 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨d, hs, run⟩ := ric_next run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [word, self] at hd
  subst d
  exact swapInputsDecoded_inv run

/-- A successful internal SafeMath `mul` call (entry 58) inside a cut walk. -/
theorem swapMulCall_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {dd y x ρ : B256} {f : SFunc} {seg : Seg}
    (run : SFunc.RunCut cert.prog sevm [] (St b (dd :: y :: x :: ρ :: R) M G) (.callNext 58 f) seg) :
    B256.Nofm x y ∧ ∃ G', SFunc.RunCut cert.prog sevm [] (St b ((x * y) :: R) M G') f seg := by
  obtain ⟨_, ⟨D, callee, run⟩ | ⟨D, callee, _⟩⟩ := ric_call (g := t_21e8_c58) rfl run
  · obtain ⟨nowrap, G', returned⟩ := mul58_inv callee
    cases returned
    exact ⟨nowrap, G', run⟩
  · obtain ⟨_, _, returned⟩ := mul58_inv callee
    cases returned

/-- A successful internal SafeMath `sub` call (entry 59) inside a cut walk. -/
theorem swapSubCall_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {dd y x ρ : B256} {f : SFunc} {seg : Seg}
    (run : SFunc.RunCut cert.prog sevm [] (St b (dd :: y :: x :: ρ :: R) M G) (.callNext 59 f) seg) :
    y ≤ x ∧ ∃ G', SFunc.RunCut cert.prog sevm [] (St b ((x - y) :: R) M G') f seg := by
  obtain ⟨_, ⟨D, callee, run⟩ | ⟨D, callee, _⟩⟩ := ric_call (g := t_226e_c59) rfl run
  · obtain ⟨cover, G', returned⟩ := sub59_inv callee
    cases returned
    exact ⟨cover, G', run⟩
  · obtain ⟨_, _, returned⟩ := sub59_inv callee
    cases returned

/-- The raw facts the successful SafeMath `K` check exposes. -/
structure SwapKFacts (bal0 bal1 in0 in1 r0 r1 : B256) : Prop where
  in0Mul : B256.Nofm in0 3
  bal0Mul : B256.Nofm bal0 1000
  cover0 : in0 * 3 ≤ bal0 * 1000
  in1Mul : B256.Nofm in1 3
  bal1Mul : B256.Nofm bal1 1000
  cover1 : in1 * 3 ≤ bal1 * 1000
  adjustedMul : B256.Nofm (bal0 * 1000 - in0 * 3) (bal1 * 1000 - in1 * 3)
  k : ¬ (bal0 * 1000 - in0 * 3) * (bal1 * 1000 - in1 * 3) <
    (reserveMask112 &&& r0) * (r1 &&& reserveMask112) * 1000000

/-- The checked adjusted balances and the `K` comparison, up to the `_update` call. -/
theorem swapK_inv {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {in1 in0 bal1 bal0 r1 r0 : B256} {seg : Seg}
    (run : SFunc.RunCut cert.prog sevm []
      (St b (in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: S) M G) t_0bd5_c8 seg) :
    SwapKFacts bal0 bal1 in0 in1 r0 r1 ∧ ∃ G',
      SFunc.RunCut cert.prog sevm []
        (St b ((bal1 * 1000 - in1 * 3) :: (bal0 * 1000 - in0 * 3) ::
          in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: S) M G') t_0cd6_c8 seg := by
  unfold t_0bd5_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨in0Mul, _, run⟩ := swapMulCall_inv run
  unfold t_0beb_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨bal0Mul, _, run⟩ := swapMulCall_inv run
  unfold t_0bfd_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨cover0, _, run⟩ := swapSubCall_inv run
  unfold t_0c09_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨in1Mul, _, run⟩ := swapMulCall_inv run
  unfold t_0beb_c8_1 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨bal1Mul, _, run⟩ := swapMulCall_inv run
  unfold t_0bfd_c8_1 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨cover1, _, run⟩ := swapSubCall_inv run
  unfold t_0c21_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, _, run⟩ := swapMulCall_inv run
  unfold t_0c4d_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, _, run⟩ := swapMulCall_inv run
  unfold t_0c59_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨adjustedMul, _, run⟩ := swapMulCall_inv run
  unfold t_0c69_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_lt hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branch run with ⟨_, _, failed⟩ | ⟨accepted, G', run⟩
  · exact (failed.false_of_noOk (by decide : t_0c70_c8.noOk = true)).elim
  · exact ⟨⟨in0Mul, bal0Mul, cover0, in1Mul, bal1Mul, cover1, adjustedMul,
      swap_not_lt_of_ltCheck_eq (eq_zero_of_iszero_ne_zero accepted)⟩, G', run⟩

end Blanc.Lift.UniswapV2Pair
