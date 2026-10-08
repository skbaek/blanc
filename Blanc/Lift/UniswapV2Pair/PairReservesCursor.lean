import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.GetterStorageReservesCore

/-! Actual packed reserve-helper cursor transport for Pair entrypoints. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Literal original-bytecode reserve-helper line before its return. -/
def pairReserveLine : List Ninst := [
  .push [8] (by decide), .reg .sload,
  .push [255,255,255,255,255,255,255,255,255,255,255,255,255,255] (by decide),
  .reg (.dup 0), .reg (.dup 2), .reg .and, .reg (.swap 2),
  .push [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide),
  .reg (.dup 3), .reg .div, .reg (.swap 0), .reg (.swap 1), .reg .and,
  .reg (.swap 1),
  .push [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide),
  .reg (.swap 0), .reg .div, .push [255,255,255,255] (by decide),
  .reg .and, .reg (.swap 0)]

/-- The actual reserve helper returns the three cached reserve words through
its supplied parent continuation, preserving the full world and memory. -/
theorem pair_reserves_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {ρ : B256} {K : List SFunc} {tail : SFunc}
    (cut : CursorStateAt code cert root t_0d90_c56 b (ρ :: R) M (tail :: K))
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root tail (afterSload root.sevm b 8)
      (reserveTimestampRead (b.getStorVal root.sevm.currentTarget 8) ::
       reserve1Read (b.getStorVal root.sevm.currentTarget 8) ::
       reserve0Read (b.getStorVal root.sevm.currentTarget 8) :: R) M K) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨returned⟩ := opened.line cert_check success fork pairReserveLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [pairReserveLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := afterSload root.sevm b 8)
    (S' := ρ :: reserveTimestampRead (b.getStorVal root.sevm.currentTarget 8) ::
      reserve1Read (b.getStorVal root.sevm.currentTarget 8) ::
      reserve0Read (b.getStorVal root.sevm.currentTarget 8) :: R) (M' := M) (by
      intro g d line
      dsimp only [pairReserveLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_div step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_div step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_swap rfl step
      cases line
      refine ⟨g', ?_⟩
      dsimp only [List.set] at state
      simpa only [reserveTimestampRead, reserve1Read, reserve0Read,
        show Bytes.toB256 [8] = (8 : B256) from rfl,
        show Bytes.toB256 [255,255,255,255,255,255,255,255,255,255,255,255,255,255] = reserveMask112 from rfl,
        show Bytes.toB256 [255,255,255,255] = reserveMask32 from rfl,
        show Bytes.toB256 [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] = reserveDiv112 from rfl,
        show Bytes.toB256 [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] = reserveDiv224 from rfl,
        B256.and_comm] using state)
  exact returned.ret cert_check success fork

end Blanc.Lift.UniswapV2Pair
