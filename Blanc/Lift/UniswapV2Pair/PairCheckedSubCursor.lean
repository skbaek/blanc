import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorSourceRun
import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.UniswapV2Pair.WriterArithmetic

/-! Actual Pair checked subtraction and its suspended continuation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairSubGuardLine : List Ninst := [
  .reg (.dup 0), .reg (.dup 2), .reg .sub, .reg (.dup 2), .reg (.dup 1),
  .reg .gt, .reg .iszero, .push [0x0d,0xf6] (by decide)]

def pairCheckedReturnLine : List Ninst := [
  .reg (.swap 2), .reg (.swap 1), .reg .pop, .reg .pop]

/-- Checked subtraction returns through the actual pending continuation.
No-underflow is inferred from that same successful cursor's source suffix. -/
theorem pair_sub59_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {x y ρ : B256} {K : List SFunc} {tail : SFunc}
    (cut : CursorStateAt code cert root t_226e_c59 b (y :: x :: ρ :: R) M (tail :: K))
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    y ≤ x ∧ Nonempty (CursorStateAt code cert root tail b ((x - y) :: R) M K) := by
  obtain ⟨outcome, source⟩ := cut.placed.sourceRun cert_check
    (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  obtain ⟨G, state⟩ := cut.state
  rw [cut.tree, state, cut.sevm_eq] at source
  have cover := (sub59_inv (source.mono (fun step => step.toRun))).1
  have gtZero : B256.gtCheck (x - y) x = 0 := by
    apply ite_eq_right
    change ¬ x < x - y
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_sub_eq_of_le x y cover]
    omega
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨guard⟩ := opened.line cert_check success fork pairSubGuardLine rfl
    (by intro n member z equal; subst n
        simp only [pairSubGuardLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x0df6 :: 1 :: (x - y) :: y :: x :: ρ :: R) (M' := M) (by
      intro g d line
      dsimp only [pairSubGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := y) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := x) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := x - y) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) gtZero (ri_gt step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨returned⟩ := guard.toSucc cert_check success fork (by decide) (by rfl)
  obtain ⟨returned⟩ := returned.dest cert_check success fork
  obtain ⟨returner⟩ := returned.line cert_check success fork pairCheckedReturnLine rfl
    (by intro n member z equal; subst n
        simp only [pairCheckedReturnLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := ρ :: (x - y) :: R) (M' := M) (by
      intro g d line
      dsimp only [pairCheckedReturnLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap (S' := ρ :: y :: x :: (x - y) :: R) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap (S' := x :: y :: ρ :: (x - y) :: R) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_pop step
      cases line
      exact ⟨g', state⟩)
  exact ⟨cover, returner.ret cert_check success fork⟩

end Blanc.Lift.UniswapV2Pair
