import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.UniswapV2Pair.FeeMintArithmetic

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The checked multiplication returns through its supplied actual continuation.
No-wrap is derived from the same actual callee, with arbitrary caller tail/K. -/
theorem pair_checked_mul_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {caller : SFunc} {x y ρ : B256}
    (cut : CursorStateAt code cert root t_21e8_c58 b (y :: x :: ρ :: R) M (caller :: K))
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    B256.Nofm x y ∧ Nonempty (CursorStateAt code cert root caller b ((x * y) :: R) M K) := by
  obtain ⟨returned, cursor, gap, env, outcome, placed, tree, conts, run⟩ :=
    cut.placed.quietReturn cert_check (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
      (E := [9, 18]) (caller := caller) (K := K) (by decide) (by decide)
      (by rw [cut.tree]; decide) (by rw [cut.tree]; decide) cut.continuations
  obtain ⟨gas, state⟩ := cut.state
  rw [cut.sevm_eq, cut.tree, state] at run
  obtain ⟨nowrap, residual, result⟩ := mul58_inv run
  have full : returned.devm = St b ((x * y) :: R) M residual := Outcome.returned.inj result
  exact ⟨nowrap, ⟨⟨returned, cursor, cut.free.trans gap, env.trans cut.sevm_eq,
    outcome.trans cut.exn_eq, placed, tree, ⟨residual, full⟩, conts⟩⟩⟩

end Blanc.Lift.UniswapV2Pair
