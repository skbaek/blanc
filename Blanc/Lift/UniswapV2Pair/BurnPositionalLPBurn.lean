import Blanc.Lift.UniswapV2Pair.PairLPBurnCursor
import Blanc.Lift.UniswapV2Pair.BurnPositionalPayout
import Blanc.Lift.UniswapV2Pair.BurnPositionalPricing
import Blanc.Lift.UniswapV2Pair.BurnPositionalPayment

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnLPCalleeLine : List Ninst := [
  .push [0x16,0x8d] (by decide), .reg .address, .reg (.dup 4), .push [0x29,0x92] (by decide)]
def burnFirstTransferCalleeLine : List Ninst := [
  .push [0x16,0x98] (by decide), .reg (.dup 7), .reg (.dup 13),
  .reg (.dup 13), .push [0x1f,0xdb] (by decide)]

/-- The priced caller burns cached LP liquidity, then reaches the actual first
transfer helper with the unchanged payout and receiver words. -/
theorem burn_lp_first_transfer_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (cut : CursorStateAt code cert root t_1683_c13 b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    ∃ residual, Nonempty (CursorStateAt code cert root t_1fdb_c57
      (lpBurnPost root.sevm b
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M root.sevm.currentTarget.toB256 L residual)
      (amount0 :: toWord :: token0 :: 0x1698 ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (lpBurnPost root.sevm b
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        M root.sevm.currentTarget.toB256 L residual).memory (t_1698_c13 :: K)) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork burnLPCalleeLine rfl
    (by intro n member x equal; subst n; simp only [burnLPCalleeLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x2992 :: L :: root.sevm.currentTarget.toB256 :: 0x168d ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
    (M' := M) (by
      intro G d line
      dsimp only [burnLPCalleeLine, burnPricedLocals] at line ⊢
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x16,0x8d] = (0x168d : B256) from rfl] at line
      obtain ⟨d, step, line⟩ := Line.of_run_cons line
      have address := of_run_address step
      have stack : d.stack = root.sevm.currentTarget.toB256 :: 0x168d ::
          supply :: f :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 ::
          amount1 :: amount0 :: toWord :: extρ :: R := address.stack
      have equal := St.of_stackRel address
      rw [stack] at equal
      rw [equal] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := L) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  obtain ⟨callee⟩ := caller.call cert_check success fork rfl
  obtain ⟨_, _, _, residual, ⟨returned⟩⟩ := pair_lp_burn_cursor_state callee success fork mem
  obtain ⟨opened⟩ := returned.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork burnFirstTransferCalleeLine rfl
    (by intro n member x equal; subst n; simp only [burnFirstTransferCalleeLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := 0x1fdb :: amount0 :: toWord :: token0 :: 0x1698 ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
    (by
      intro G d line
      dsimp only [burnFirstTransferCalleeLine, burnPricedLocals] at line ⊢
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x16,0x98] = (0x1698 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := token0) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := toWord) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := amount0) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  exact ⟨residual, caller.call cert_check success fork rfl⟩

/-- Successful original pricing derives all guards consumed by the actual
product/division/LP transports, without adding those guards to its callers. -/
theorem burn_pricing_first_transfer_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert root t_15e2_c37 b
      (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    let supply := b.getStorVal root.sevm.currentTarget 0
    let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
      ((L * b1) / supply) ((L * b0) / supply) toWord extρ R
    ∃ residual, Nonempty (CursorStateAt code cert root t_1fdb_c57
      (lpBurnPost root.sevm (afterSload root.sevm b 0) locals M
        root.sevm.currentTarget.toB256 L residual)
      (((L * b0) / supply) :: toWord :: token0 :: 0x1698 :: locals)
      (lpBurnPost root.sevm (afterSload root.sevm b 0) locals M
        root.sevm.currentTarget.toB256 L residual).memory (t_1698_c13 :: K)) := by
  obtain ⟨_, _, nonzero, positive0, positive1⟩ := burn_pricing_guards_of_cursor cut success fork
  obtain ⟨_, ⟨first⟩⟩ := burn_pricing_first_product_cursor_state cut success fork
  obtain ⟨_, ⟨second⟩⟩ := burn_second_product_cursor_state first success fork nonzero
  obtain ⟨priced⟩ := burn_payout_cursor_state second success fork nonzero positive0 positive1
  exact burn_lp_first_transfer_cursor_state priced success fork mem

end Blanc.Lift.UniswapV2Pair
