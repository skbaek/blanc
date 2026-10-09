import Blanc.Lift.UniswapV2Pair.BurnPositionalThree
import Blanc.Lift.UniswapV2Pair.PairFeeReturn
import Blanc.Lift.UniswapV2Pair.BurnPositionalLPBurn

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnThreeCalls.feeReturnLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) : List B256 :=
  burnFeeLocals (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm)
    (Bytes.toB256 (r.initial.out1.take 32)) (Bytes.toB256 (r.initial.out0.take 32))
    (burnInitialToken1 sevm b) (burnInitialToken0 sevm b)
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
    (Sevm.dataWord sevm 4).toAdr.toB256 0x053d [0x89afcb44]

/-- The fee return, pricing cursor and physical state belong to one actual node. -/
structure BurnFeeReturnData {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) where
  memory : PtrMem 128 192 N.devm.memory
  cut : CursorStateAt code cert r.fee.occurrence.call.returned t_15e2_c37 N.devm
    (feeOnWord (Bytes.toB256 (r.fee.out.take 32)) :: r.feeReturnLocals)
    N.devm.memory [t_053d_c83]
  node_eq : cut.node = N
  guards : feeBranchAccepts r.initial.second.returned.sevm
    (feeKLastWorld r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (feeKLastWord r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)
  state : ∃ gas, N.devm = feeBranchPost r.initial.second.returned.sevm
    (feeKLastWorld r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    r.feeReturnLocals
    (feeReplyMemory (feeBurnMemory (burnInitialReplyMemory sevm r.initial.out0 r.initial.out1)
      r.initial.second.returned.sevm.currentTarget) r.fee.out)
    (feeKLastWord r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b) gas

/-- Literal payout locals retain the original sampled balances and liquidity. -/
def BurnThreeCalls.pricedLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) : List B256 :=
  let supply := N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0
  let L := feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm
  let b1 := Bytes.toB256 (r.initial.out1.take 32)
  let b0 := Bytes.toB256 (r.initial.out0.take 32)
  burnPricedLocals supply (feeOnWord (Bytes.toB256 (r.fee.out.take 32))) L b1 b0
    (burnInitialToken1 sevm b) (burnInitialToken0 sevm b)
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
    ((L * b1) / supply) ((L * b0) / supply)
    (Sevm.dataWord sevm 4).toAdr.toB256 0x053d [0x89afcb44]

/-- The actual fee reply returns through pricing and LP burn into the first
transfer helper, preserving the complete returned fee world and physical memory. -/
theorem BurnThreeCalls.firstTransferCalleeData {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    (r : BurnThreeCalls root sevm b) (success : root.exn = .ok post)
    (fork : CoveredFork sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (residual : Nat), Nonempty (BurnFeeReturnData r N) ∧
      Nonempty (CursorStateAt code cert r.fee.occurrence.call.returned t_1fdb_c57
        (lpBurnPost r.fee.occurrence.call.returned.sevm
          (afterSload r.fee.occurrence.call.returned.sevm N.devm 0)
          (r.pricedLocals N) N.devm.memory
          r.fee.occurrence.call.returned.sevm.currentTarget.toB256
          (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual)
        (((feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
            Bytes.toB256 (r.initial.out0.take 32)) /
            N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0) ::
          (Sevm.dataWord sevm 4).toAdr.toB256 :: burnInitialToken0 sevm b ::
          0x1698 :: r.pricedLocals N)
        (lpBurnPost r.fee.occurrence.call.returned.sevm
          (afterSload r.fee.occurrence.call.returned.sevm N.devm 0)
          (r.pricedLocals N) N.devm.memory
          r.fee.occurrence.call.returned.sevm.currentTarget.toB256
          (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual).memory
        [t_1698_c13, t_053d_c83]) := by
  have startEnv : r.initial.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.initial.second.edge).trans r.initial.second_sevm
  have startSuccess : r.initial.second.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq
      (r.initial.second.sameFrame.snoc r.initial.second.edge)).trans success
  have bound0 : (burnInitialReserve0 sevm b).toNat < 2 ^ 112 := by
    unfold burnInitialReserve0 reserve0Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have bound1 : (burnInitialReserve1 sevm b).toNat < 2 ^ 112 := by
    unfold burnInitialReserve1 reserve1Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have mem := balanceReplyMemory_ptr r.initial.out1
    (balanceRequestMemory_ptr
      (balanceReplyMemory_ptr r.initial.out0
        (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)) sevm.currentTarget)
  obtain ⟨N, memory, pricing, pricingNode, guards, gas, state⟩ := r.fee.returnCutData startSuccess
    (by rw [startEnv]; exact fork) (feeBurnMemory_ptr mem _) bound0 bound1
  have returnedSuccess : r.fee.occurrence.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq
      (r.fee.occurrence.call.sameFrame.snoc r.fee.occurrence.call.edge)).trans success
  have returnedEnv : r.fee.occurrence.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.fee.occurrence.call.edge).trans
      (r.fee.occurrence.sevm_eq.trans startEnv)
  have pricingCut := burn_pricing_first_transfer_cursor_state
    (by simpa only [burnFeeLocals] using pricing) returnedSuccess
    (by rw [returnedEnv]; exact fork) memory
  obtain ⟨residual, callee⟩ := pricingCut
  exact ⟨N, residual, ⟨⟨memory, pricing, pricingNode, guards, gas, state⟩⟩,
    by simpa only [BurnThreeCalls.pricedLocals] using callee⟩

end Blanc.Lift.UniswapV2Pair
