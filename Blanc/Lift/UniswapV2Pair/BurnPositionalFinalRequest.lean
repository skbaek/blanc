import Blanc.Lift.UniswapV2Pair.BurnPositionalTransfers

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnFinalFirstCodeGuardTree : SFunc :=
  syncCodeGuardLine.foldr SFunc.next
    (.next (.push [0x17, 0x0f] (by decide)) (.branch t_170b_c13 t_170f_c13))

/-- The original final first request Line advances the supplied actual cursor. -/
theorem burn_final_first_preparation_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {p : B256}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (cut : CursorStateAt code cert start t_16a3_c13 b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (ptr : PtrWord p M) (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    Nonempty (CursorStateAt code cert start burnFinalFirstCodeGuardTree b
      ((token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (skimRequestMemory M p start.sevm.currentTarget) K) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  exact opened.line cert_check success fork burnFinalFirstRequestLine rfl
    (by intro n member x equal; subst n
        simp only [burnFinalFirstRequestLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (burnFinalFirstRequestLine_inv ptr low high)

def burnFinalSecondCodeGuardTree : SFunc :=
  syncCodeGuardLine.foldr SFunc.next
    (.next (.push [0x17, 0xab] (by decide)) (.branch t_17a7_c13 t_17ab_c13))

/-- The original final second request Line advances the supplied actual cursor. -/
theorem burn_final_second_preparation_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {p : B256}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ balance0 : B256}
    (cut : CursorStateAt code cert start BurnFinalBalanceSite.first.afterDecodeTree b
      (balance0 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (ptr : PtrWord p M) (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    Nonempty (CursorStateAt code cert start burnFinalSecondCodeGuardTree b
      ((token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        burnPricedLocals supply f L b1 balance0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (skimRequestMemory M p start.sevm.currentTarget) K) := by
  exact cut.line cert_check success fork burnFinalSecondRequestLine rfl
    (by intro n member x equal; subst n
        simp only [burnFinalSecondRequestLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (burnFinalSecondRequestLine_inv ptr low high)

end Blanc.Lift.UniswapV2Pair
