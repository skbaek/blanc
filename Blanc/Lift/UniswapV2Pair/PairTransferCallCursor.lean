import Blanc.Lift.CursorGasCall
import Blanc.Lift.UniswapV2Pair.PairTransferPreparation

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The original physical post-CALL branch retains full returndata for its
allocation and optional-bool decoder. -/
def pairTransferAfterCallTree : SFunc :=
  .next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop)
    (.next (.reg .returndatasize) (.next (.reg (.dup 0)) (.next (.push [0] (by decide))
      (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.push [0x21,0x43] (by decide))
        (.branch t_2122_c57 t_2143_c57)))))))))

def pairTransferGasTree : SFunc := .next (.reg .gas) (.next (.exec .call) pairTransferAfterCallTree)

/-- The actual partial merge prepares the exact physical CALL stack and memory;
its remaining gas is inferred from the supplied successful execution. -/
theorem pair_transfer_partial_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {src dst a x y z w token : B256}
    (cut : CursorStateAt code cert start t_20e1_c57 b
      (src :: dst :: 4 :: a :: x :: y :: z :: w :: token :: R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    let mask := B256.bexp 256 (32 - 4) - 1
    let M1 := (M.read src.toNat 32).2
    let M2 := (M1.read dst.toNat 32).2
    let M3 := M2.write dst.toNat
      (((Bytes.toB256 (M.read src.toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (M1.read dst.toNat 32).1) &&& mask)).toBytes
    let q := Bytes.toB256 (M3.read 64 32).1
    let M4 := (M3.read 64 32).2
    Nonempty (CursorStateAt code cert start pairTransferGasTree b
      (token :: 0 :: q :: ((a + y) - q) :: q :: 0 :: (a + y) :: token :: R) M4 K) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  exact opened.line cert_check success fork pairTransferPartialLine rfl
    (by intro n member e equal; subst n; simp only [pairTransferPartialLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    pair_transfer_partial_line_inv

/-- The supplied actual GAS cursor produces this original-root CALL and its
real filled slot, returned cursor and complete physical successor state. -/
theorem pair_transfer_call_of_gas_cursor {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {token q inputSize endWord : B256}
    (cut : CursorStateAt code cert start pairTransferGasTree b
      (token :: 0 :: q :: inputSize :: q :: 0 :: endWord :: token :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root .call) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧ step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St b
        (gas.toB256 :: token :: 0 :: q :: inputSize :: q :: 0 :: endWord :: token :: R) M gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec .call) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧ cursor.f = pairTransferAfterCallTree ∧
      cursor.K.map Cont.f = K :=
  cut.gasCall cert_check reached success fork

end Blanc.Lift.UniswapV2Pair
