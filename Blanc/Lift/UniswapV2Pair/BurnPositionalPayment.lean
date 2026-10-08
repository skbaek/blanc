import Blanc.Lift.UniswapV2Pair.PairCheckedMulCursor
import Blanc.Lift.UniswapV2Pair.BurnPricingWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnFirstSupplyLine : List Ninst := [.reg (.dup 1), .push [0x16,0x00] (by decide)]

def burnSecondProductLine : List Ninst := [
  .reg .div, .reg (.swap 10), .reg .pop, .reg (.dup 0),
  .push [0x16,0x14] (by decide), .reg (.dup 4), .reg (.dup 6),
  .push [0xff,0xff,0xff,0xff] (by decide), .push [0x21,0xe8] (by decide), .reg .and]

/-- The actual first quotient becomes amount0 before the second checked product.
The denominator guard is supplied by the successful pricing suffix. -/
theorem burn_second_product_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {product0 supply f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert root t_15f9_c37 b
      (product0 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 0 toWord extρ R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (nonzero : supply ≠ 0) :
    B256.Nofm L b1 ∧ Nonempty (CursorStateAt code cert root t_1614_c37 b
      ((L * b1) :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 (product0 / supply) toWord extρ R) M K) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨test⟩ := opened.line cert_check success fork burnFirstSupplyLine rfl
    (by intro n member x equal; subst n; simp only [burnFirstSupplyLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x1600 :: supply :: product0 :: supply ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 0 toWord extρ R)
    (M' := M) (by
      intro G d line
      dsimp only [burnFirstSupplyLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  obtain ⟨payment⟩ := test.branchSucc cert_check success fork nonzero
  obtain ⟨opened⟩ := payment.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork burnSecondProductLine rfl
    (by intro n member x equal; subst n; simp only [burnSecondProductLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x21e8 :: b1 :: L :: 0x1614 :: supply ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 (product0 / supply) toWord extρ R) (M' := M) (by
      intro G d line
      dsimp only [burnSecondProductLine, burnPricedLocals] at line ⊢
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_div step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl step
      dsimp only [List.set] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x16,0x14] = (0x1614 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := L) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := b1) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0xff,0xff,0xff,0xff] = (0xffffffff : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x21,0xe8] = (0x21e8 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_and step
      cases line
      exact ⟨gas, by simpa only [show (0x21e8 : B256) &&& 0xffffffff = 0x21e8 from by decide]
        using result⟩)
  obtain ⟨callee⟩ := caller.call cert_check success fork rfl
  exact pair_checked_mul_cursor_state callee success fork

end Blanc.Lift.UniswapV2Pair
