import Blanc.Lift.UniswapV2Pair.BurnPositionalFive
import Blanc.Lift.UniswapV2Pair.BurnBalanceWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnFiveCallsH.secondMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) :
    PtrMem (r.four.replyPointer + 164) r.four.secondTransferMemory.size r.four.secondTransferMemory ∧
      r.four.replyPointer.toNat + 260 ≤ r.four.secondTransferMemory.size := by
  obtain ⟨n, pointer⟩ := r.four.replyMem
  have layout := burnFirstTransferPointer_layout r.first_bound
  have lower : 128 ≤ r.four.replyPointer.toNat := by
    have low := layout.2.1
    change 128 ≤ (burnFirstTransferPointer r.four.transfer.returned.devm.returnData).toNat
    omega
  have width : r.four.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  exact ⟨safeTransfer_callMemory_ptr pointer lower width,
    safeTransfer_dynamicCall_fit pointer lower width⟩

def BurnFiveCalls.finalMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) : Mem :=
  if r.second.returned.devm.returnData = [] then r.four.secondTransferMemory else
    Blanc.Lift.bytesArrayMemory r.four.secondTransferMemory (r.four.replyPointer + 164)
      r.second.returned.devm.returnData

def BurnFiveCallsH.finalMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) : Mem :=
  if r.second.returned.devm.returnData = [] then r.four.secondTransferMemory else
    Blanc.Lift.bytesArrayMemory r.four.secondTransferMemory (r.four.replyPointer + 164)
      r.second.returned.devm.returnData

def BurnFiveCalls.finalPointer {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) : B256 :=
  burnSecondTransferPointer r.four.transfer.returned.devm.returnData r.second.returned.devm.returnData

def BurnFiveCallsH.finalPointer {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) : B256 :=
  burnSecondTransferPointer r.four.transfer.returned.devm.returnData r.second.returned.devm.returnData

theorem BurnFiveCalls.finalMemory_toH {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnFiveCalls root sevm b) :
    (r.toH fork).finalMemory = r.finalMemory := by
  unfold BurnFiveCallsH.finalMemory BurnFiveCalls.finalMemory
  show (if r.second.returned.devm.returnData = [] then (r.four.toH fork).secondTransferMemory else
    Blanc.Lift.bytesArrayMemory (r.four.toH fork).secondTransferMemory (r.four.replyPointer + 164)
      r.second.returned.devm.returnData) = _
  rw [BurnFourCalls.secondTransferMemory_toH fork]

theorem BurnFiveCallsH.finalMemory_toCovered {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnFiveCallsH root sevm b BurnSchedule.modern) :
    (r.toCovered fork).finalMemory = r.finalMemory := by
  unfold BurnFiveCallsH.finalMemory BurnFiveCalls.finalMemory
  show (if r.second.returned.devm.returnData = [] then (r.four.toCovered fork).secondTransferMemory else
    Blanc.Lift.bytesArrayMemory (r.four.toCovered fork).secondTransferMemory (r.four.replyPointer + 164)
      r.second.returned.devm.returnData) = _
  rw [BurnFourCallsH.secondTransferMemory_toCovered fork]

theorem BurnFiveCallsH.actualReply {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) (success : root.exn = .ok post)
    (stateGas : sevm.benvStat.rules.stateGas = none) :
    r.second.returned.devm.stack = 1 :: (68 + (r.four.replyPointer + 164)) ::
      (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: r.four.three.amount1 r.four.pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      burnInitialToken1 sevm b :: 0x16a3 :: r.four.three.pricedLocals r.four.pricing ∧
    r.second.returned.devm.memory = r.four.secondTransferMemory ∧
    r.second.returned.devm.output = r.four.transfer.returned.devm.output ∧
    r.second.returned.devm.returnData.length < 2 ^ 160 ∧
    (r.second.returned.devm.returnData = [] ∨
      (32 ≤ r.second.returned.devm.returnData.length ∧
        Bytes.toB256 (r.second.returned.devm.returnData.sliceD 0 32 0) ≠ 0)) ∧
    Nonempty (CursorStateAt code cert r.second.returned t_16a3_c13
      r.second.returned.devm (r.four.three.pricedLocals r.four.pricing) r.finalMemory [t_053d_c83]) := by
  have layout := burnFirstTransferPointer_layout r.first_bound
  have lower : 128 ≤ r.four.replyPointer.toNat := by
    have low := layout.2.1
    change 128 ≤ (burnFirstTransferPointer r.four.transfer.returned.devm.returnData).toNat
    omega
  have width : r.four.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  simpa only [BurnFiveCallsH.finalMemory] using
    pair_transfer_reply_cursor_stateH r.second r.input r.placed r.tree r.conts success
      (by rw [r.sevm_eq]; exact stateGas) r.secondMem.1 lower width r.secondMem.2

/-- The second actual CALL supplies its own full reply and checked final-query
caller; the prior reply determines only its moving input pointer. -/
theorem BurnFiveCalls.actualReply {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    (r : BurnFiveCalls root sevm b) (success : root.exn = .ok post)
    (fork : CoveredFork sevm.benvStat.fork) :
    r.second.returned.devm.stack = 1 :: (68 + (r.four.replyPointer + 164)) ::
      (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: r.four.three.amount1 r.four.pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      burnInitialToken1 sevm b :: 0x16a3 :: r.four.three.pricedLocals r.four.pricing ∧
    r.second.returned.devm.memory = r.four.secondTransferMemory ∧
    r.second.returned.devm.output = r.four.transfer.returned.devm.output ∧
    r.second.returned.devm.returnData.length < 2 ^ 160 ∧
    (r.second.returned.devm.returnData = [] ∨
      (32 ≤ r.second.returned.devm.returnData.length ∧
        Bytes.toB256 (r.second.returned.devm.returnData.sliceD 0 32 0) ≠ 0)) ∧
    Nonempty (CursorStateAt code cert r.second.returned t_16a3_c13
      r.second.returned.devm (r.four.three.pricedLocals r.four.pricing) r.finalMemory [t_053d_c83]) := by
  have h := BurnFiveCallsH.actualReply (r.toH fork) success fork.rules_stateGas_none

  simp only [BurnFiveCalls.finalMemory_toH fork] at h
  simp only [BurnFiveCalls.toH, BurnFourCalls.secondTransferMemory_toH fork] at h
  exact h


theorem BurnFiveCallsH.finalMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) : ∃ n, PtrMem r.finalPointer n r.finalMemory := by
  have layout := burnFirstTransferPointer_layout r.first_bound
  have width : r.four.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  have nat164 : (r.four.replyPointer + 164).toNat = r.four.replyPointer.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  by_cases empty : r.second.returned.devm.returnData = []
  · exact ⟨r.four.secondTransferMemory.size,
      by simpa only [BurnFiveCallsH.finalMemory, BurnFiveCallsH.finalPointer,
        burnSecondTransferPointer, BurnFourCallsH.replyPointer, empty, ite_true] using r.secondMem.1⟩
  · have image := Blanc.Lift.bytesArrayMemory_image (bytes := r.second.returned.devm.returnData)
      r.secondMem.1 (by rw [nat164]; have := layout.2.1; change 96 ≤ _; omega)
      (by rw [nat164]; have := r.secondMem.2; omega) (by rw [nat164]; omega)
    exact ⟨memExtSize r.four.secondTransferMemory.size (r.four.replyPointer + 164 + 32).toNat
      r.second.returned.devm.returnData.length,
      by simpa only [BurnFiveCallsH.finalMemory, BurnFiveCallsH.finalPointer,
        burnSecondTransferPointer, BurnFourCallsH.replyPointer, ite_eq_right empty] using image.1⟩

end Blanc.Lift.UniswapV2Pair
