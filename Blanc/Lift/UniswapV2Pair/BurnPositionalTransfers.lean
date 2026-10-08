import Blanc.Lift.UniswapV2Pair.BurnPositionalFive
import Blanc.Lift.UniswapV2Pair.BurnBalanceWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnFiveCalls.secondMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) :
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

def BurnFiveCalls.finalPointer {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) : B256 :=
  burnSecondTransferPointer r.four.transfer.returned.devm.returnData r.second.returned.devm.returnData

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
  have layout := burnFirstTransferPointer_layout r.first_bound
  have lower : 128 ≤ r.four.replyPointer.toNat := by
    have low := layout.2.1
    change 128 ≤ (burnFirstTransferPointer r.four.transfer.returned.devm.returnData).toNat
    omega
  have width : r.four.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  simpa only [BurnFiveCalls.finalMemory] using
    pair_transfer_reply_cursor_state r.second r.input r.placed r.tree r.conts success
      (by rw [r.sevm_eq]; exact fork) r.secondMem.1 lower width r.secondMem.2

/-- The final query pointer is the physical result of both actual allocations,
with no stored zero-sentinel premise. -/
theorem BurnFiveCalls.finalMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) : ∃ n, PtrMem r.finalPointer n r.finalMemory := by
  have layout := burnFirstTransferPointer_layout r.first_bound
  have width : r.four.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  have nat164 : (r.four.replyPointer + 164).toNat = r.four.replyPointer.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  by_cases empty : r.second.returned.devm.returnData = []
  · exact ⟨r.four.secondTransferMemory.size,
      by simpa only [BurnFiveCalls.finalMemory, BurnFiveCalls.finalPointer,
        burnSecondTransferPointer, BurnFourCalls.replyPointer, empty, ite_true] using r.secondMem.1⟩
  · have image := Blanc.Lift.bytesArrayMemory_image (bytes := r.second.returned.devm.returnData)
      r.secondMem.1 (by rw [nat164]; have := layout.2.1; change 96 ≤ _; omega)
      (by rw [nat164]; have := r.secondMem.2; omega) (by rw [nat164]; omega)
    exact ⟨memExtSize r.four.secondTransferMemory.size (r.four.replyPointer + 164 + 32).toNat
      r.second.returned.devm.returnData.length,
      by simpa only [BurnFiveCalls.finalMemory, BurnFiveCalls.finalPointer,
        burnSecondTransferPointer, BurnFourCalls.replyPointer, ite_eq_right empty] using image.1⟩

end Blanc.Lift.UniswapV2Pair
