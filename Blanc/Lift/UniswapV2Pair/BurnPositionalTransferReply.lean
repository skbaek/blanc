import Blanc.Lift.UniswapV2Pair.BurnPositionalFour
import Blanc.Lift.UniswapV2Pair.PairTransferReplyCursor

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The retained actual pricing memory fixes the first transfer's physical
request allocation, without a memory-shape premise on the public producer. -/
theorem BurnFourCalls.transferMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) :
    PtrMem 292 416 (r.three.transferMemory r.pricing r.residual) := by
  have lpMem : PtrMem 128 192 (r.three.transferWorld r.pricing r.residual).memory :=
    pairLPBurnPost_ptr r.pricing_memory
  have pointer := safeTransfer_callMemory_ptr (amount := r.three.amount0 r.pricing)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) lpMem (by decide) (by decide)
  have size := (safeTransfer_copySizes (amount := r.three.amount0 r.pricing)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) lpMem (by decide) (by decide)).1
  have fixedSize : safeTransferPreSize 192 128 = 416 := by
    norm_num only [safeTransferPreSize, List.foldl, memExtSize, ceilDiv,
      ite_true, ite_false, Nat.max_def, show (128 : B256).toNat = 128 from rfl]
  simpa only [BurnThreeCalls.transferMemory, size,
    show (128 + 164 : B256) = 292 from by decide,
    fixedSize] using pointer

def BurnFourCalls.replyMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : Mem :=
  if r.transfer.returned.devm.returnData = [] then r.three.transferMemory r.pricing r.residual
  else Blanc.Lift.bytesArrayMemory (r.three.transferMemory r.pricing r.residual) 292
    r.transfer.returned.devm.returnData

/-- The first original transfer's own reply supplies the actual caller state
and full physical allocation used by transfer1. -/
theorem BurnFourCalls.actualReply {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    (r : BurnFourCalls root sevm b) (success : root.exn = .ok post)
    (fork : CoveredFork sevm.benvStat.fork) :
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
  have reply := pair_transfer_reply_cursor_state r.transfer input r.returnedPlaced
    r.returnedTree r.returnedConts success (by rw [r.transfer_sevm]; exact fork)
    memory (by decide) (by decide) (by decide)
  simpa only [BurnFourCalls.replyMemory, show (128 + 164 : B256) = 292 from by decide] using reply

end Blanc.Lift.UniswapV2Pair
