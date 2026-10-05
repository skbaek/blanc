import Blanc.Lift.UniswapV2Pair.BurnDispatchWalk
import Blanc.Lift.UniswapV2Pair.GetterStringWalk

/-! Forward liveness construction for the Uniswap V2 Pair `burn` entry.

The selector route is kept as a small reusable boundary: later stages attach the ABI
wrapper, fee/pricing prefix, transfers, final balance observations, and source frame.
-/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal Burn selector route, after the public value/size guards. -/
theorem burnSelector_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (body : SFunc.RunExact cert.prog sevm (St b [0x89afcb44] M (G + 43)) t_050a_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + 166)) t_001a_c0 o := by
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_shr (v := 0x89afcb44) selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_002b_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0097) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_succ (by decide)
  unfold t_0097_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x00d3) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_00a3_c0
  apply cmp_miss (by decide)
  unfold t_00ae_c0
  exact cmp_hit (tgt := t_050a_c83) rfl (by rfl) body

/-- Burn's public nonpayable/size guards and selector dispatch. -/
theorem burnDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0x89afcb44] getterInitMemory (G + 43)) t_050a_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 229)) t_0000_c0 o := by
  exact getterString_guards_exact value size (burnSelector_exact selector body)

end Blanc.Lift.UniswapV2Pair
