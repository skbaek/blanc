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

def BurnThreeCallsH.feeReturnLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) : List B256 :=
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

structure BurnFeeReturnDataH {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) where
  memory : PtrMem 128 192 N.devm.memory
  cut : CursorStateAt code cert r.fee.occurrence.call.returned t_15e2_c37 N.devm
    (feeOnWord (Bytes.toB256 (r.fee.out.take 32)) :: r.feeReturnLocals)
    N.devm.memory [t_053d_c83]
  node_eq : cut.node = N
  guards : feeBranchAcceptsH r.initial.second.returned.sevm
    (feeKLastWorldH r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (feeKLastWord r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)
  state : ∃ gas, N.devm = feeBranchPostH r.initial.second.returned.sevm
    (feeKLastWorldH r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    r.feeReturnLocals
    (feeReplyMemory (feeBurnMemory (burnInitialReplyMemory sevm r.initial.out0 r.initial.out1)
      r.initial.second.returned.sevm.currentTarget) r.fee.out)
    (feeKLastWord r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b) gas

/-- At the modern call worlds and on a covered fork, `BurnFeeReturnDataH` gives the modern
`BurnFeeReturnData` over the converted calls. -/
def BurnFeeReturnDataH.toCoveredOf {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {r : BurnThreeCallsH root sevm b BurnSchedule.modern} {N : Exec.Deriv}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnFeeReturnDataH r N) :
    BurnFeeReturnData (r.toCovered fork) N where
  memory := h.memory
  cut := h.cut
  node_eq := h.node_eq
  guards := by
    have f : CoveredFork r.initial.second.returned.sevm.benvStat.fork := by
      rw [r.initial.returned_sevm]; exact fork
    have g := h.guards
    rw [feeBranchAcceptsH_of_covered f, feeKLastWorldH_of_covered f] at g
    exact g
  state := by
    have f : CoveredFork r.initial.second.returned.sevm.benvStat.fork := by
      rw [r.initial.returned_sevm]; exact fork
    have g := h.state
    simp only [feeBranchPostH_of_covered f, feeKLastWorldH_of_covered f] at g
    exact g

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

def BurnThreeCallsH.pricedLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) : List B256 :=
  let supply := N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0
  let L := feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm
  let b1 := Bytes.toB256 (r.initial.out1.take 32)
  let b0 := Bytes.toB256 (r.initial.out0.take 32)
  burnPricedLocals supply (feeOnWord (Bytes.toB256 (r.fee.out.take 32))) L b1 b0
    (burnInitialToken1 sevm b) (burnInitialToken0 sevm b)
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
    ((L * b1) / supply) ((L * b0) / supply)
    (Sevm.dataWord sevm 4).toAdr.toB256 0x053d [0x89afcb44]

theorem BurnThreeCallsH.firstTransferCalleeData {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (success : root.exn = .ok post)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) :
    ∃ (N : Exec.Deriv) (residual : Nat), Nonempty (BurnFeeReturnDataH r N) ∧
      Nonempty (CursorStateAt code cert r.fee.occurrence.call.returned t_1fdb_c57
        (lpBurnPostH r.fee.occurrence.call.returned.sevm
          (afterSloadH r.fee.occurrence.call.returned.sevm N.devm 0)
          (r.pricedLocals N) N.devm.memory
          r.fee.occurrence.call.returned.sevm.currentTarget.toB256
          (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual)
        (((feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
            Bytes.toB256 (r.initial.out0.take 32)) /
            N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0) ::
          (Sevm.dataWord sevm 4).toAdr.toB256 :: burnInitialToken0 sevm b ::
          0x1698 :: r.pricedLocals N)
        (lpBurnPostH r.fee.occurrence.call.returned.sevm
          (afterSloadH r.fee.occurrence.call.returned.sevm N.devm 0)
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
    (by rw [startEnv]; exact stateGas) (by rw [startEnv]; exact bal) (feeBurnMemory_ptr mem _) bound0 bound1
  have returnedSuccess : r.fee.occurrence.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq
      (r.fee.occurrence.call.sameFrame.snoc r.fee.occurrence.call.edge)).trans success
  have returnedEnv : r.fee.occurrence.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.fee.occurrence.call.edge).trans
      (r.fee.occurrence.sevm_eq.trans startEnv)
  have pricingCut := burn_pricing_first_transfer_cursor_stateH
    (by simpa only [burnFeeLocals] using pricing) returnedSuccess
    (by rw [returnedEnv]; exact stateGas) (by rw [returnedEnv]; exact bal) memory
  obtain ⟨residual, callee⟩ := pricingCut
  exact ⟨N, residual, ⟨⟨memory, pricing, pricingNode, guards, gas, state⟩⟩,
    by simpa only [BurnThreeCallsH.pricedLocals] using callee⟩


end Blanc.Lift.UniswapV2Pair
