import Blanc.Lift.UniswapV2Pair.PairCheckedMulCursor
import Blanc.Lift.UniswapV2Pair.BurnPricingWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnSecondSupplyLine : List Ninst := [.reg (.dup 1), .push [0x16,0x1b] (by decide)]
def burnFirstPayoutGuardLine : List Ninst := [
  .reg .div, .reg (.swap 9), .reg .pop, .push [0x00] (by decide),
  .reg (.dup 11), .reg .gt, .reg (.dup 0), .reg .iszero,
  .push [0x16,0x2e] (by decide)]
def burnSecondPayoutGuardLine : List Ninst := [
  .reg .pop, .push [0x00] (by decide), .reg (.dup 10), .reg .gt]
def burnPayoutTargetLine : List Ninst := [.push [0x16,0x83] (by decide)]

/-- Both payout words survive the actual short-circuit checks and reach LP burn.
The positive-word guards are those derived from this same successful suffix. -/
theorem burn_payout_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {product1 supply f L b1 b0 token1 token0 r1 r0 amount0 toWord extρ : B256}
    (cut : CursorStateAt code cert root t_1614_c37 b
      (product1 :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 amount0 toWord extρ R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (nonzero : supply ≠ 0) (positive0 : 0 < amount0.toNat)
    (positive1 : 0 < (product1 / supply).toNat) :
    Nonempty (CursorStateAt code cert root t_1683_c13 b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        (product1 / supply) amount0 toWord extρ R) M K) := by
  have word0 : (0 : B256) < amount0 := by
    rw [B256.lt_iff_toNat_lt_toNat]; exact positive0
  have word1 : (0 : B256) < product1 / supply := by
    rw [B256.lt_iff_toNat_lt_toNat]; exact positive1
  have gt0 : B256.gtCheck amount0 0 = 1 := by simp only [B256.gtCheck, word0, ite_eq_left]
  have gt1 : B256.gtCheck (product1 / supply) 0 = 1 := by
    simp only [B256.gtCheck, word1, ite_eq_left]
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨test⟩ := opened.line cert_check success fork burnSecondSupplyLine rfl
    (by intro n member x equal; subst n; simp only [burnSecondSupplyLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x161b :: supply :: product1 :: supply ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 amount0 toWord extρ R)
    (M' := M) (by
      intro G d line
      dsimp only [burnSecondSupplyLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  obtain ⟨payment⟩ := test.branchSucc cert_check success fork nonzero
  obtain ⟨opened⟩ := payment.dest cert_check success fork
  obtain ⟨guard0⟩ := opened.line cert_check success fork burnFirstPayoutGuardLine rfl
    (by intro n member x equal; subst n; simp only [burnFirstPayoutGuardLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x162e :: 0 :: 1 ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        (product1 / supply) amount0 toWord extρ R) (M' := M) (by
      intro G d line
      dsimp only [burnFirstPayoutGuardLine, burnPricedLocals] at line ⊢
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_div step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl step
      dsimp only [List.set] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := amount0) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, result⟩ := ri_gt step
      rw [gt0] at result
      subst result
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, result⟩ := ri_iszero step
      rw [show B256.eqCheck 1 0 = (0 : B256) from by decide] at result
      subst result
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  obtain ⟨short⟩ := guard0.toZero cert_check success fork
  obtain ⟨guard1⟩ := short.line cert_check success fork burnSecondPayoutGuardLine rfl
    (by intro n member x equal; subst n; simp only [burnSecondPayoutGuardLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 1 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
      (product1 / supply) amount0 toWord extρ R) (M' := M) (by
      intro G d line
      dsimp only [burnSecondPayoutGuardLine, burnPricedLocals] at line ⊢
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := product1 / supply) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_gt step
      cases line
      exact ⟨gas, by simpa only [gt1] using result⟩)
  obtain ⟨opened⟩ := guard1.dest cert_check success fork
  obtain ⟨target⟩ := opened.line cert_check success fork burnPayoutTargetLine rfl
    (by intro n member x equal; subst n; simp only [burnPayoutTargetLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x1683 :: 1 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
      (product1 / supply) amount0 toWord extρ R) (M' := M) (by
      intro G d line
      dsimp only [burnPayoutTargetLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  exact target.branchSucc cert_check success fork (by decide : (1 : B256) ≠ 0)

end Blanc.Lift.UniswapV2Pair
