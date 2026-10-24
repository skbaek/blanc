import Blanc.Lift.UniswapV2Pair.BurnPositionalFour
import Blanc.Lift.UniswapV2Pair.PairTransferReplyCursor

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnFourCallsH.transferMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) :
    PtrMem 292 416 (r.three.transferMemory r.pricing r.residual) := by
  have lpMem : PtrMem 128 192 (r.three.transferWorld r.pricing r.residual).memory :=
    pairLPBurnPost_ptrH r.pricing_memory
  have pointer := safeTransfer_callMemory_ptr (amount := r.three.amount0 r.pricing)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) lpMem (by decide) (by decide)
  have size := (safeTransfer_copySizes (amount := r.three.amount0 r.pricing)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) lpMem (by decide) (by decide)).1
  have fixedSize : safeTransferPreSize 192 128 = 416 := by
    norm_num only [safeTransferPreSize, List.foldl, memExtSize, ceilDiv,
      ite_true, ite_false, Nat.max_def, show (128 : B256).toNat = 128 from rfl]
  simpa only [BurnThreeCallsH.transferMemory_eq, size,
    show (128 + 164 : B256) = 292 from by decide,
    fixedSize] using pointer

def BurnFourCalls.replyMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : Mem :=
  if r.transfer.returned.devm.returnData = [] then r.three.transferMemory r.pricing r.residual
  else Blanc.Lift.bytesArrayMemory (r.three.transferMemory r.pricing r.residual) 292
    r.transfer.returned.devm.returnData

def BurnFourCallsH.replyMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) : Mem :=
  if r.transfer.returned.devm.returnData = [] then r.three.transferMemory r.pricing r.residual
  else Blanc.Lift.bytesArrayMemory (r.three.transferMemory r.pricing r.residual) 292
    r.transfer.returned.devm.returnData

theorem BurnFourCallsH.replyMemory_toCovered {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnFourCallsH root sevm b BurnSchedule.modern) :
    (r.toCovered fork).replyMemory = r.replyMemory := by
  unfold BurnFourCallsH.replyMemory BurnFourCalls.replyMemory
  show (if r.transfer.returned.devm.returnData = [] then
      (r.three.toCovered fork).transferMemory r.pricing r.residual
    else Blanc.Lift.bytesArrayMemory ((r.three.toCovered fork).transferMemory r.pricing r.residual) 292
      r.transfer.returned.devm.returnData) = _
  rw [BurnThreeCallsH.transferMemory_toCovered fork]

theorem BurnFourCallsH.actualReply {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) (success : root.exn = .ok post)
    (stateGas : sevm.benvStat.rules.stateGas = none) :
    r.transfer.returned.devm.stack = 1 :: 360 ::
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: r.three.amount0 r.pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      burnInitialToken0 sevm b :: 0x1698 :: r.three.pricedLocals r.pricing ∧
    r.transfer.returned.devm.memory = r.three.transferMemory r.pricing r.residual ∧
    r.transfer.returned.devm.output = (r.three.transferWorld r.pricing r.residual).output ∧
    r.transfer.returned.devm.returnData.length < 2 ^ 160 ∧
    (r.transfer.returned.devm.returnData = [] ∨
      (32 ≤ r.transfer.returned.devm.returnData.length ∧
        Bytes.toB256 (r.transfer.returned.devm.returnData.sliceD 0 32 0) ≠ 0)) ∧
    Nonempty (CursorStateAt code cert r.transfer.returned t_1698_c13
      r.transfer.returned.devm (r.three.pricedLocals r.pricing) r.replyMemory [t_053d_c83]) := by
  have input : r.transfer.occurrence.node.devm = St (r.three.transferWorld r.pricing r.residual)
      (r.gas.toB256 :: (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (128 + 164) :: 68 :: (128 + 164) :: 0 :: 360 ::
        (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: r.three.amount0 r.pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
        burnInitialToken0 sevm b :: 0x1698 :: r.three.pricedLocals r.pricing)
      (r.three.transferMemory r.pricing r.residual) r.gas := by
    simpa only [show (128 + 164 : B256) = 292 from by decide] using r.transfer_input
  have memory : PtrMem (128 + 164) 416 (r.three.transferMemory r.pricing r.residual) := by
    simpa only [show (128 + 164 : B256) = 292 from by decide] using r.transferMem
  have reply := pair_transfer_reply_cursor_stateH r.transfer input r.returnedPlaced
    r.returnedTree r.returnedConts success (by rw [r.transfer_sevm]; exact stateGas)
    memory (by decide) (by decide) (by decide)
  simpa only [BurnFourCallsH.replyMemory, show (128 + 164 : B256) = 292 from by decide] using reply


end Blanc.Lift.UniswapV2Pair
