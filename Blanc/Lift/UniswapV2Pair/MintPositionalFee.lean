import Blanc.Lift.UniswapV2Pair.MintPositionalAmounts
import Blanc.Lift.UniswapV2Pair.PairCheckedSubCursor
import Blanc.Lift.UniswapV2Pair.PairFeeObservation

/-! Mint's actual third external instruction after its checked amounts. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem mint_amounts_fee_cursor_stateH {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {b1 b0 r1 r0 toWord ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start MintBalanceSite.second.afterDecodeTree b
      (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M K)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) :
    r0 ≤ b0 ∧ r1 ≤ b1 ∧
      Nonempty (CursorStateAt code cert start t_26ec_c68 b
        (r1 :: r0 :: 0x1233 ::
          mintFeeLocals (b1 - r1) (b0 - r0) b1 b0 r1 r0 toWord ρ R)
        M (t_1233_c41 :: K)) := by
  obtain ⟨callee0⟩ := mint_amount0_callee_cursor_stateH cut success stateGas bound0
  obtain ⟨cover0, caller1⟩ := pair_sub59_cursor_stateH callee0 success stateGas
  obtain ⟨caller1⟩ := caller1
  obtain ⟨callee1⟩ := mint_amount1_callee_cursor_stateH caller1 success stateGas bound1
  obtain ⟨cover1, feeCaller⟩ := pair_sub59_cursor_stateH callee1 success stateGas
  obtain ⟨feeCaller⟩ := feeCaller
  exact ⟨cover0, cover1, mint_fee_callee_cursor_stateH feeCaller success stateGas⟩

/-- Both checked amounts and the fee caller preserve the whole actual world,
memory and pending caller continuation through this exec-free span. -/
theorem mint_amounts_fee_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {b1 b0 r1 r0 toWord ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start MintBalanceSite.second.afterDecodeTree b
      (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) :
    r0 ≤ b0 ∧ r1 ≤ b1 ∧
      Nonempty (CursorStateAt code cert start t_26ec_c68 b
        (r1 :: r0 :: 0x1233 ::
          mintFeeLocals (b1 - r1) (b0 - r0) b1 b0 r1 r0 toWord ρ R)
        M (t_1233_c41 :: K)) :=
  mint_amounts_fee_cursor_stateH cut success fork.rules_stateGas_none bound0 bound1


end Blanc.Lift.UniswapV2Pair
