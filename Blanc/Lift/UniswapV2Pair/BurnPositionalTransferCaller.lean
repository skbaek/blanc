import Blanc.Lift.UniswapV2Pair.BurnPositionalLPBurn

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnSecondTransferCalleeLine : List Ninst := [
  .push [0x16,0xa3] (by decide), .reg (.dup 6), .reg (.dup 13),
  .reg (.dup 12), .push [0x1f,0xdb] (by decide)]

/-- The second transfer caller retains the cached payout and the complete
world and physical memory left by the first actual token reply. -/
theorem burn_second_transfer_callee_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (cut : CursorStateAt code cert start t_1698_c13 b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert start t_1fdb_c57 b
      (amount1 :: toWord :: token1 :: 0x16a3 ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      M (t_16a3_c13 :: K)) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork burnSecondTransferCalleeLine rfl
    (by intro n member x equal; subst n; simp only [burnSecondTransferCalleeLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := 0x1fdb :: amount1 :: toWord :: token1 :: 0x16a3 ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
    (by
      intro G d line
      dsimp only [burnSecondTransferCalleeLine, burnPricedLocals] at line ⊢
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x16,0xa3] = (0x16a3 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := token1) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := toWord) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := amount1) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_push step
      cases line
      exact ⟨gas, result⟩)
  exact caller.call cert_check success fork rfl

end Blanc.Lift.UniswapV2Pair
