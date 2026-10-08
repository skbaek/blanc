import Blanc.Lift.CursorJump
import Blanc.Lift.UniswapV2Pair.PairTransferPreparation

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairTransferCopyGuardLine : List Ninst :=
  [.push [0x20] (by decide), .reg (.dup 3), .reg .lt, .push [0x20,0xe1] (by decide)]

/-- The original copy guard reads the actual remaining-length word. -/
theorem pair_transfer_copy_guard_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {src dst len : B256}
    (cut : CursorStateAt code cert root t_20a4_c57 b (src :: dst :: len :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root (.branch t_20ad_c57 t_20e1_c57) b
      (0x20e1 :: B256.ltCheck len 32 :: src :: dst :: len :: R) M K) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  apply opened.line cert_check success fork pairTransferCopyGuardLine rfl
    (by intro n member x equal; subst n; simp only [pairTransferCopyGuardLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
  intro G d line
  dsimp only [pairTransferCopyGuardLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := len) rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨gas, state⟩

/-- One actual copy pass follows its checked referenced JUMP and retains K. -/
theorem pair_transfer_copy_pass_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {src dst len : B256}
    (cut : CursorStateAt code cert root t_20a4_c57 b (src :: dst :: len :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (enough : ¬ len < (32 : B256)) :
    Nonempty (CursorStateAt code cert root t_20a4_c57 b
      ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
      ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes) K) := by
  obtain ⟨guard⟩ := pair_transfer_copy_guard_cursor_state cut success fork
  have zero : B256.ltCheck len 32 = 0 := by simp only [B256.ltCheck, ite_eq_right enough]
  rw [zero] at guard
  obtain ⟨body⟩ := guard.branchZero cert_check success fork
  obtain ⟨jump⟩ := body.line cert_check success fork pairTransferCopyLine rfl
    (by intro n member x equal; subst n; simp only [pairTransferCopyLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    pair_transfer_copy_line_inv
  exact jump.goto cert_check success fork rfl

/-- The final actual guard exits the loop with the remaining partial word. -/
theorem pair_transfer_copy_exit_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {src dst len : B256}
    (cut : CursorStateAt code cert root t_20a4_c57 b (src :: dst :: len :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (short : len < (32 : B256)) :
    Nonempty (CursorStateAt code cert root t_20e1_c57 b (src :: dst :: len :: R) M K) := by
  obtain ⟨guard⟩ := pair_transfer_copy_guard_cursor_state cut success fork
  have one : B256.ltCheck len 32 = 1 := by simp only [B256.ltCheck, ite_eq_left short]
  rw [one] at guard
  exact guard.branchSucc cert_check success fork (by decide : (1 : B256) ≠ 0)

/-- The supplied actual 68-byte copy cursor performs two passes, then exits at
four bytes. Each span retains its selected physical read/store image. -/
theorem pair_transfer_copy68_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {src dst : B256}
    (cut : CursorStateAt code cert root t_20a4_c57 b (src :: dst :: 68 :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    let M1 := (M.read src.toNat 32).2.write dst.toNat
      (Bytes.toB256 (M.read src.toNat 32).1).toBytes
    let M2 := (M1.read (32 + src).toNat 32).2.write (32 + dst).toNat
      (Bytes.toB256 (M1.read (32 + src).toNat 32).1).toBytes
    Nonempty (CursorStateAt code cert root t_20e1_c57 b
      ((32 + (32 + src)) :: (32 + (32 + dst)) :: 4 :: R) M2 K) := by
  obtain ⟨first⟩ := pair_transfer_copy_pass_cursor_state cut success fork
    (by decide : ¬ (68 : B256) < 32)
  rw [show (68 : B256) + ~~~31 = 36 from rfl] at first
  obtain ⟨second⟩ := pair_transfer_copy_pass_cursor_state first success fork
    (by decide : ¬ (36 : B256) < 32)
  rw [show (36 : B256) + ~~~31 = 4 from rfl] at second
  exact pair_transfer_copy_exit_cursor_state second success fork (by decide : (4 : B256) < 32)

end Blanc.Lift.UniswapV2Pair
