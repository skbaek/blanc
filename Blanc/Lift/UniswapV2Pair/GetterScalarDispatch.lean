import Blanc.Lift.UniswapV2Pair.GetterScalarCore
import Blanc.Lift.InvWalkDispatch

/-! Actual selector-tree paths for the ten scalar getter entries. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem getterScalar_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (s : ScalarGetter) (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (body : SFunc.RunExact cert.prog sevm (St b [s.selector] getterInitMemory G) s.entryTree o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + s.dispatchGas)) t_0000_c0 o := by
  cases s with
  | constant s =>
    cases s with
    | decimals =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 146) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0x313ce567) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00f9_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0105_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_0140_c0
      refine rx_dest ?_
      refine cmp_miss (by decide) ?_
      unfold t_014c_c0
      refine cmp_miss (by decide) ?_
      unfold t_0157_c0
      exact cmp_hit (tgt := t_03f8_c95) rfl (by rfl) body
    | minimumLiquidity =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 101) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0xba9a7a56) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_002b_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0036_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x71) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_0071_c0
      refine rx_dest ?_
      exact cmp_hit (tgt := t_0597_c79) rfl (by rfl) body
    | permitTypehash =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 124) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0x30adf81f) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00f9_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0105_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_0140_c0
      refine rx_dest ?_
      refine cmp_miss (by decide) ?_
      unfold t_014c_c0
      exact cmp_hit (tgt := t_03f0_c94) rfl (by rfl) body
  | stored s =>
    cases s with
    | domainSeparator =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 101) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0x3644e515) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00f9_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0105_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0110_c0
      exact cmp_hit (tgt := t_0416_c89) rfl (by rfl) body
    | price0CumulativeLast =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 145) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0x5909c0d5) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00f9_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0105_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0110_c0
      refine cmp_miss (by decide) ?_
      unfold t_011b_c0
      refine cmp_miss (by decide) ?_
      unfold t_0126_c0
      exact cmp_hit (tgt := t_0459_c91) rfl (by rfl) body
    | price1CumulativeLast =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 167) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0x5a3d5493) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00f9_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0105_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0110_c0
      refine cmp_miss (by decide) ?_
      unfold t_011b_c0
      refine cmp_miss (by decide) ?_
      unfold t_0126_c0
      refine cmp_miss (by decide) ?_
      unfold t_0131_c0
      exact cmp_hit (tgt := t_0461_c92) rfl (by rfl) body
    | kLast =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 146) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0x7464fc3d) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_002b_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_0097_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xd3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00d3_c0
      refine rx_dest ?_
      refine cmp_miss (by decide) ?_
      unfold t_00df_c0
      refine cmp_miss (by decide) ?_
      unfold t_00ea_c0
      exact cmp_hit (tgt := t_04cf_c88) rfl (by rfl) body
  | address s =>
    cases s with
    | factory =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 145) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0xc45a0155) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_002b_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0036_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x71) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_0071_c0
      refine rx_dest ?_
      refine cmp_miss (by decide) ?_
      unfold t_007d_c0
      refine cmp_miss (by decide) ?_
      unfold t_0088_c0
      exact cmp_hit (tgt := t_05d2_c81) rfl (by rfl) body
    | token0 =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 124) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0xdfe1681) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_00f9_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_succ (by decide) ?_
      unfold t_0166_c0
      refine rx_dest ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x95ea7b3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x197) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0172_c0
      refine cmp_miss (by decide) ?_
      unfold t_017d_c0
      exact cmp_hit (tgt := t_0362_c97) rfl (by rfl) body
    | token1 =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree, ScalarGetter.dispatchGas] at selector body ⊢
      refine getterString_guards_exact (G := G + 100) value size ?_
      unfold t_001a_c0
      refine rx_push (w := 0) rfl (by decide) ?_
      refine rx_calldataload (by decide) ?_
      refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_shr (v := 0xd21220a7) selector (by decide) ?_
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_002b_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0036_c0
      refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_push (w := 0x71) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
      refine rx_branch_zero ?_
      unfold t_0041_c0
      exact cmp_hit (tgt := t_05da_c75) rfl (by rfl) body

theorem getterScalar_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (s : ScalarGetter) (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.Run cert.prog sevm (St b [s.selector] M G') s.entryTree o := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = s.selector from selector] at hd
  subst d
  cases s with
  | constant s =>
    cases s with
    | decimals =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x313ce567 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00f9_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x313ce567 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x313ce567 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_0140_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03ad_c93) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x313ce567 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_014c_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f0_c94) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x30, 0xad, 0xf8, 0x1f]) (0x313ce567 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0157_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f8_c95) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x31, 0x3c, 0xe5, 0x67]) (0x313ce567 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | minimumLiquidity =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xba9a7a56 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_002b_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xba9a7a56 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0036_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xba9a7a56 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_0071_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0597_c79) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xba9a7a56 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | permitTypehash =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x30adf81f : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00f9_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x30adf81f : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x30adf81f : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_0140_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03ad_c93) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x30adf81f : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_014c_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f0_c94) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x30, 0xad, 0xf8, 0x1f]) (0x30adf81f : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
  | stored s =>
    cases s with
    | domainSeparator =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x3644e515 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00f9_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x3644e515 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x3644e515 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0110_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0416_c89) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x3644e515 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | price0CumulativeLast =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x5909c0d5 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00f9_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x5909c0d5 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x5909c0d5 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0110_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0416_c89) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x5909c0d5 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_011b_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_041e_c90) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x48, 0x5c, 0xc9, 0x55]) (0x5909c0d5 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0126_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0459_c91) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x59, 0x9, 0xc0, 0xd5]) (0x5909c0d5 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | price1CumulativeLast =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x5a3d5493 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00f9_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x5a3d5493 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x5a3d5493 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0110_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0416_c89) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x5a3d5493 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_011b_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_041e_c90) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x48, 0x5c, 0xc9, 0x55]) (0x5a3d5493 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0126_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0459_c91) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x59, 0x9, 0xc0, 0xd5]) (0x5a3d5493 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0131_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0461_c92) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x5a, 0x3d, 0x54, 0x93]) (0x5a3d5493 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | kLast =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x7464fc3d : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_002b_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0x7464fc3d : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_0097_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x0]) (0x7464fc3d : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00d3_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0469_c86) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x7464fc3d : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_00df_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_049c_c87) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]) (0x7464fc3d : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_00ea_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04cf_c88) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x74, 0x64, 0xfc, 0x3d]) (0x7464fc3d : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
  | address s =>
    cases s with
    | factory =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xc45a0155 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_002b_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xc45a0155 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0036_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xc45a0155 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_0071_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0597_c79) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xc45a0155 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_007d_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_059f_c80) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0xbc, 0x25, 0xcf, 0x77]) (0xc45a0155 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0088_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05d2_c81) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0xc4, 0x5a, 0x1, 0x55]) (0xc45a0155 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | token0 =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xdfe1681 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_00f9_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0xdfe1681 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      unfold t_0166_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x9, 0x5e, 0xa7, 0xb3]) (0xdfe1681 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0172_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0315_c96) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0x9, 0x5e, 0xa7, 0xb3]) (0xdfe1681 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_017d_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0362_c97) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0xd, 0xfe, 0x16, 0x81]) (0xdfe1681 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩
    | token1 =>
      simp only [ScalarGetter.selector, ScalarGetter.entryTree] at h ⊢
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xd21220a7 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_002b_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xd21220a7 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0036_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xd21220a7 : B256) = (0 : B256) from by decide, ite_true] at h
      unfold t_0041_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05da_c75) (by intro bad; cases bad) (by rfl) h
      simp only [show B256.eqCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xd21220a7 : B256) = (1 : B256) from by decide,
    show (1 : B256) ≠ 0 from by decide, ite_false] at h
      exact ⟨_, h.uncut⟩


end Blanc.Lift.UniswapV2Pair
