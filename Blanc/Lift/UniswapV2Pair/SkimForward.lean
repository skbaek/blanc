import Blanc.Lift.UniswapV2Pair.SkimCanonical
import Blanc.Lift.UniswapV2Pair.SwapForwardTransfer
import Blanc.Lift.UniswapV2Pair.SwapForwardBalance
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.ExactWalkSolc

/-! Forward (gas-exact) prefix of the skim entry: the PC0 guards, the selector
dispatch to `t_059f_c80`, the ABI head guard of wrapper80 and the lock read of
entry34. The mirror of `skimSelector_inv`, `skimWrapper_inv` and `skimLock_inv`;
the two transfers reuse the shared `_safeTransfer` hypothesis
(`SwapSafeTransferForward`, owned by the parallel worker) and the two
`balanceOf` queries reuse `SwapBalanceEnv`, so nothing generic is proved here. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Reshape a forward goal's gas so variable charges unify outermost. -/
private theorem skimFwd_gas {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G G' : Nat} {f : SFunc} {o : Outcome} (h : G = G')
    (k : SFunc.RunExact fs sevm (St b S M G') f o) :
    SFunc.RunExact fs sevm (St b S M G) f o := h ▸ k

/-- The literal skim selector path: 123 gas from `t_001a_c0` to wrapper80. -/
theorem skimDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0xbc25cf77] getterInitMemory G) t_059f_c80 o) :
    SFunc.RunExact cert.prog sevm (St b [] getterInitMemory (G + 123)) t_001a_c0 o := by
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_shr selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_002b_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0097) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_0036_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0071) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_0071_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_eq (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0597) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branchTo_zero
  unfold t_007d_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xbc25cf77) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_eq (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x059f) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  exact rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl body

/-- Wrapper80 forward: under the ABI head guard it masks the recipient word and
enters entry34; 63 gas. -/
theorem skimWrapper_exact {sevm : Sevm} {b : Devm} {G : Nat} {sel : B256} {o : Outcome}
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (body : SFunc.RunExact cert.prog sevm
      (St b [skimToWord sevm, 0x0257, sel] getterInitMemory G) t_18de_c34 o) :
    SFunc.RunExact cert.prog sevm (St b [sel] getterInitMemory (G + 63)) t_059f_c80 o := by
  have hle : (32 : B256).toNat ≤ (sevm.data.length.toB256 - 4).toNat :=
    B256.le_iff_toNat_le_toNat.mp abi
  have hlt : B256.ltCheck (sevm.data.length.toB256 - 4) 32 = 0 := by
    have nlt : ¬ (sevm.data.length.toB256 - 4) < 32 := by
      rw [B256.lt_iff_toNat_lt_toNat]
      omega
    simp only [B256.ltCheck, nlt, ite_false]
  unfold t_059f_c80
  apply rx_dest
  apply rx_push (w := 0x0257) rfl (by simp only [List.length_cons]; decide)
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; decide)
  apply rx_dup1 (by simp only [List.length_cons]; decide)
  apply rx_calldatasize (by simp only [List.length_cons]; decide)
  apply rx_sub (by simp only [List.length_cons]; decide)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; decide)
  apply rx_dup (n := 1) rfl (by simp only [List.length_cons]; decide)
  apply rx_lt (v := 0) hlt (by simp only [List.length_cons]; decide)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; decide)
  apply rx_push (w := 0x05b5) rfl (by simp only [List.length_cons]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_05b5_c80
  apply rx_dest
  apply rx_pop
  apply rx_calldataload (by simp only [List.length_cons]; decide)
  apply rx_push (w := 0xffffffffffffffffffffffffffffffffffffffff) rfl
    (by simp only [List.length_cons]; decide)
  apply rx_and (ff20_and_word _) (by simp only [List.length_cons]; decide)
  apply rx_push (w := 0x18de) rfl (by simp only [List.length_cons]; decide)
  exact rx_jump rfl body

/-- Entry34 lock read forward: under the unlocked store it enters `t_194f_c34`. -/
theorem skimLock_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G s12 : Nat} {toWord : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (c12 : s12 = sloadCost sevm b 12) (room : R.length ≤ 1000)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 12) (toWord :: R) M G) t_194f_c34 o) :
    SFunc.RunExact cert.prog sevm
      (St b (toWord :: R) M (G + s12 + 23)) t_18de_c34 o := by
  have heq : B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) = 1 := by
    rw [unlocked]
    decide
  unfold t_18de_c34
  apply skimFwd_gas (G' := ((G + 19) + s12) + 4) (by omega)
  apply rx_dest
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork c12 (by simp only [List.length_cons]; omega)
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_eq heq (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x194f) rfl (by simp only [List.length_cons]; omega)
  refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
  exact body

end Blanc.Lift.UniswapV2Pair
