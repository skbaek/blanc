import Blanc.Lift.CursorGasCall
import Blanc.Lift.UniswapV2Pair.MintPositionalAmounts
import Blanc.Lift.UniswapV2Pair.PairCheckedSubCursor
import Blanc.Lift.UniswapV2Pair.PairFeeCursor

/-! Mint's actual third external instruction after its checked amounts. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintFeeAfterCallTree : SFunc :=
  .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
    (.next (.push [0x27,0x6b] (by decide)) (.branch t_2762_c68 t_276b_c68))))

/-- The actual factory instruction, its request world, original slot and
returned cursor, all selected under the same supplied root. -/
structure MintFeeOccurrence (root start : Exec.Deriv) (b : Devm) (factory : B256)
    (S : List B256) (M : Mem) (K : List SFunc) where
  call : CallOccurrenceStep root .staticcall
  cursor : Cursor
  gas : Nat
  free : Exec.Deriv.ExecFreeUntil start call.occurrence.node
  sevm_eq : call.occurrence.node.sevm = start.sevm
  exn_eq : call.occurrence.node.exn = start.exn
  input : call.occurrence.node.devm = St b
    (gas.toB256 :: factory :: 128 :: 4 :: 128 :: 32 :: S) M gas
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) start.sevm
    call.occurrence.node.devm (.exec .staticcall) call.returned.devm
  code_exists : (b.getCode factory.toAdr).size.toB256 ≠ 0
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = mintFeeAfterCallTree
  continuations : cursor.K.map Cont.f = K

/-- The shared checked fee caller reaches its real STATICCALL with the code
guard proved from its actual successful suffix. -/
theorem mint_fee_occurrence_of_callee {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start t_26ec_c68 b (r1 :: r0 :: ρ :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    Nonempty (MintFeeOccurrence root start (feeFactoryCallWorld start.sevm b)
      (feeFactoryWord start.sevm b)
      (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) K) := by
  obtain ⟨prepared⟩ := pair_fee_preparation_cursor_state cut success fork mem
  obtain ⟨nonzero, guarded⟩ := pair_fee_code_cursor_state prepared success fork
  obtain ⟨guarded⟩ := guarded
  obtain ⟨opened⟩ := guarded.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] rfl
    (by intro n member x equal; subst n; simp at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      exact ri_pop step)
  obtain ⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, K⟩ :=
    beforeGas.gasCall cert_check reached success fork
  refine ⟨⟨call, cursor, gas, free, env, outcome, input, primitive, ?_, placed, tree, K⟩⟩
  simpa only [feeFactoryCallWorld, Devm.getCode, Devm.getAcct,
    temporalAccountAccessBase_state] using nonzero

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
        M (t_1233_c41 :: K)) := by
  obtain ⟨callee0⟩ := mint_amount0_callee_cursor_state cut success fork bound0
  obtain ⟨cover0, caller1⟩ := pair_sub59_cursor_state callee0 success fork
  obtain ⟨caller1⟩ := caller1
  obtain ⟨callee1⟩ := mint_amount1_callee_cursor_state caller1 success fork bound1
  obtain ⟨cover1, feeCaller⟩ := pair_sub59_cursor_state callee1 success fork
  obtain ⟨feeCaller⟩ := feeCaller
  exact ⟨cover0, cover1, mint_fee_callee_cursor_state feeCaller success fork⟩

end Blanc.Lift.UniswapV2Pair
