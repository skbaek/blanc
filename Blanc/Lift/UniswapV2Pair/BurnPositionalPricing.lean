import Blanc.Lift.CursorSourceRun
import Blanc.Lift.UniswapV2Pair.PairCheckedMulCursor
import Blanc.Lift.UniswapV2Pair.BurnPricingWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Successful original pricing supplies its own product and payout guards. -/
theorem burn_pricing_guards_of_cursor {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert root t_15e2_c37 b
      (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    let supply := b.getStorVal root.sevm.currentTarget 0
    B256.Nofm L b0 ∧ B256.Nofm L b1 ∧ supply ≠ 0 ∧
      0 < ((L * b0) / supply).toNat ∧ 0 < ((L * b1) / supply).toNat := by
  obtain ⟨outcome, run⟩ := cut.placed.sourceRun cert_check (cut.exn_eq.trans success)
    (cut.sevm_eq ▸ fork)
  obtain ⟨gas, state⟩ := cut.state
  rw [cut.sevm_eq, cut.tree, state] at run
  obtain ⟨product0, product1, nonzero, positive0, positive1, _⟩ :=
    burnPricingWords_inv (fun step => StepIn.toRun step) fork (by decide : 13 ∉ [])
      (SFunc.runP_iff_runCutP_nil.mp run)
  exact ⟨product0, product1, nonzero, positive0, positive1⟩

def burnPricingFirstLine : List Ninst := [
  .push [0x00] (by decide), .reg .sload, .reg (.swap 0), .reg (.swap 1), .reg .pop,
  .reg (.dup 0), .push [0x15,0xf9] (by decide), .reg (.dup 4), .reg (.dup 7),
  .push [0xff,0xff,0xff,0xff] (by decide), .push [0x21,0xe8] (by decide), .reg .and]

/-- Post-fee supply and the first product are read and computed along the actual
pricing caller, retaining the cached pre-fee liquidity and all later locals. -/
theorem burn_pricing_first_product_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert root t_15e2_c37 b
      (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    let supply := b.getStorVal root.sevm.currentTarget 0
    B256.Nofm L b0 ∧ Nonempty (CursorStateAt code cert root t_15f9_c37
      (afterSload root.sevm b 0)
      ((L * b0) :: supply :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0
        0 0 toWord extρ R) M K) := by
  let supply := b.getStorVal root.sevm.currentTarget 0
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork burnPricingFirstLine rfl
    (by intro n member x equal; subst n
        simp only [burnPricingFirstLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (b' := afterSload root.sevm b 0)
    (S' := 0x21e8 :: b0 :: L :: 0x15f9 :: supply ::
      burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 0 0 toWord extρ R)
    (M' := M) (by
      intro G d line
      dsimp only [burnPricingFirstLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_sload fork step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl step
      dsimp only [List.set] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl step
      dsimp only [List.set] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x15,0xf9] = (0x15f9 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := L) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := b0) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0xff,0xff,0xff,0xff] = (0xffffffff : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      rw [show Bytes.toB256 [0x21,0xe8] = (0x21e8 : B256) from rfl] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas, result⟩ := ri_and step
      cases line
      exact ⟨gas, by simpa only [supply, burnPricedLocals,
        show (0x21e8 : B256) &&& 0xffffffff = 0x21e8 from by decide] using result⟩)
  obtain ⟨callee⟩ := caller.call cert_check success fork rfl
  exact pair_checked_mul_cursor_state callee success fork

end Blanc.Lift.UniswapV2Pair
