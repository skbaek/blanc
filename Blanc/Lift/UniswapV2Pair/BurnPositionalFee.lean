import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorGasCall
import Blanc.Lift.UniswapV2Pair.PairFeeCursor
import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk
import Blanc.Lift.UniswapV2Pair.FeeMintSource

/-! Actual Burn liquidity sampling and the factory fee observation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnLiquiditySamplingLine : List Ninst := [
  .reg .address,
  .push [0x00] (by decide),
  .reg (.swap 0),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x01] (by decide),
  .push [0x20] (by decide),
  .reg .mstore,
  .push [0x40] (by decide),
  .reg (.dup 1),
  .reg .keccak256,
  .reg .sload,
  .reg (.swap 1),
  .reg (.swap 2),
  .reg .pop,
  .push [0x15, 0xe2] (by decide),
  .reg (.dup 8),
  .reg (.dup 8),
  .push [0x26, 0xec] (by decide)]

/-- The pair LP balance is sampled by the actual original caller before fee68.
No representation, chosen fee result, or caller gas schedule is needed here. -/
theorem burn_fee_caller_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {b1 discarded b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert root BurnInitialBalanceSite.second.afterDecodeTree b
      (b1 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    Nonempty (CursorStateAt code cert root t_26ec_c68 (feeBurnWorld root.sevm b)
      (r1 :: r0 :: 0x15e2 :: burnFeeLocals (feeBurnLiquidity root.sevm b)
        b1 b0 token1 token0 r1 r0 toWord extρ R)
      (feeBurnMemory M root.sevm.currentTarget) (t_15e2_c37 :: K)) := by
  let sevm := root.sevm
  have scratch := feeBurnMemory_ptr mem sevm.currentTarget
  obtain ⟨caller⟩ := cut.line cert_check success fork burnLiquiditySamplingLine rfl
    (by intro n member x equal; subst n
        simp only [burnLiquiditySamplingLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (b' := feeBurnWorld root.sevm b)
    (S' := 0x26ec :: r1 :: r0 :: 0x15e2 ::
      burnFeeLocals (feeBurnLiquidity root.sevm b) b1 b0 token1 token0 r1 r0 toWord extρ R)
    (M' := feeBurnMemory M root.sevm.currentTarget) (by
      intro G d line
      dsimp only [burnLiquiditySamplingLine] at line
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      have address := of_run_address hs
      have stack : d.stack = sevm.currentTarget.toB256 :: b1 :: discarded ::
          b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R := by
        have h := address.stack
        change d.stack = sevm.currentTarget.toB256 :: b1 :: discarded ::
          b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R at h
        exact h
      have eq := St.of_stackRel address
      rw [stack] at eq
      rw [eq] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push hs
      rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_mstore hs
      rw [show (0 : B256).toNat = 0 from rfl] at eq
      subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push hs
      rw [show Bytes.toB256 [1] = (1 : B256) from rfl] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push hs
      rw [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at line
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_mstore hs
      rw [show (32 : B256).toNat = 32 from rfl] at eq
      subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push hs
      rw [show Bytes.toB256 [0x40] = (64 : B256) from rfl] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_keccak hs
      change d = St b
        (((feeBurnMemory M sevm.currentTarget).read 0 64).1.keccak :: 0 :: b1 :: discarded ::
          b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        ((feeBurnMemory M sevm.currentTarget).read 0 64).2 _ at eq
      rw [feeBurnMemory_hash, scratch.read_self (by decide : 0 + 64 ≤ 192)] at eq
      subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_sload fork hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_pop hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push hs
      rw [show Bytes.toB256 [0x15, 0xe2] = (0x15e2 : B256) from by decide] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨gas, state⟩ := ri_push hs
      cases line
      exact ⟨gas, by simpa only [sevm, feeBurnWorld, feeBurnLiquidity, burnFeeLocals,
        show Bytes.toB256 [0x26,0xec] = (0x26ec : B256) from rfl] using state⟩)
  exact caller.call cert_check success fork rfl

end Blanc.Lift.UniswapV2Pair
