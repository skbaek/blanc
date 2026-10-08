import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk

/-! Actual Mint checked-subtraction caller cuts. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintAmount0CallerLine : List Ninst := [
  .reg (.swap 0),
  .reg .pop,
  .push [0x00] (by decide),
  .push [0x12, 0x01] (by decide),
  .reg (.dup 3),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 7),
  .reg .and,
  .push [0xff, 0xff, 0xff, 0xff] (by decide),
  .push [0x22, 0x6e] (by decide),
  .reg .and]

/-- Mint's literal amount0 caller preserves the actual helper and continuation. -/
theorem mint_amount0_callee_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {b1 b0 r1 r0 toWord ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root MintBalanceSite.second.afterDecodeTree b
      (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (bound : r0.toNat < 2 ^ 112) :
    Nonempty (CursorStateAt code cert root t_226e_c59 b
      (r0 :: b0 :: 0x1201 :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M (t_1201_c41 :: K)) := by
  obtain ⟨caller⟩ := cut.line cert_check success fork mintAmount0CallerLine rfl
    (by intro n member x equal; subst n
        simp only [mintAmount0CallerLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x226e :: r0 :: b0 :: 0x1201 :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) (M' := M) (by
      intro G d line
      dsimp only [mintAmount0CallerLine] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := b0) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hs
      rw [show r0 &&& Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = r0 from feeReserveWord_eq bound] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_and hs
      rw [show Bytes.toB256 [0x22,0x6e] &&& Bytes.toB256 [0xff,0xff,0xff,0xff] = (0x226e : B256) from by decide] at state
      cases line
      exact ⟨gas, by simpa only [show Bytes.toB256 [0x12,0x01] = (0x1201 : B256) from rfl,
        show Bytes.toB256 [0] = (0 : B256) from rfl] using state⟩)
  exact caller.call cert_check success fork (by rfl)

def mintAmount1CallerLine : List Ninst := [
  .reg (.swap 0),
  .reg .pop,
  .push [0x00] (by decide),
  .push [0x12, 0x25] (by decide),
  .reg (.dup 3),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 7),
  .reg .and,
  .push [0xff, 0xff, 0xff, 0xff] (by decide),
  .push [0x22, 0x6e] (by decide),
  .reg .and]

/-- Mint's literal amount1 caller preserves the actual helper and continuation. -/
theorem mint_amount1_callee_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {b1 b0 r1 r0 toWord ρ amount0 : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_1201_c41 b
      (amount0 :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (bound : r1.toNat < 2 ^ 112) :
    Nonempty (CursorStateAt code cert root t_226e_c59 b
      (r1 :: b1 :: 0x1225 :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M (t_1225_c41 :: K)) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork mintAmount1CallerLine rfl
    (by intro n member x equal; subst n
        simp only [mintAmount1CallerLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := 0x226e :: r1 :: b1 :: 0x1225 :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) (M' := M) (by
      intro G d line
      dsimp only [mintAmount1CallerLine] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := b1) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hs
      rw [show r1 &&& Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = r1 from feeReserveWord_eq bound] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_and hs
      rw [show Bytes.toB256 [0x22,0x6e] &&& Bytes.toB256 [0xff,0xff,0xff,0xff] = (0x226e : B256) from by decide] at state
      cases line
      exact ⟨gas, by simpa only [show Bytes.toB256 [0x12,0x25] = (0x1225 : B256) from rfl,
        show Bytes.toB256 [0] = (0 : B256) from rfl] using state⟩)
  exact caller.call cert_check success fork (by rfl)

def mintFeeCallerLine : List Ninst := [
  .reg (.swap 0),
  .reg .pop,
  .push [0x00] (by decide),
  .push [0x12, 0x33] (by decide),
  .reg (.dup 7),
  .reg (.dup 7),
  .push [0x26, 0xec] (by decide)]

/-- The actual Mint caller enters the shared fee helper with its real continuation. -/
theorem mint_fee_callee_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_1225_c41 b
      (amount1 :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root t_26ec_c68 b
      (r1 :: r0 :: 0x1233 :: mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R)
      M (t_1233_c41 :: K)) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨caller⟩ := opened.line cert_check success fork mintFeeCallerLine rfl
    (by intro n member x equal; subst n
        simp only [mintFeeCallerLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b)
    (S' := 0x26ec :: r1 :: r0 :: 0x1233 :: mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R)
    (M' := M) (by
      intro G d line
      dsimp only [mintFeeCallerLine] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push hs
      cases line
      exact ⟨gas, state⟩)
  exact caller.call cert_check success fork (by rfl)

end Blanc.Lift.UniswapV2Pair
