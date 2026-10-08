import Blanc.Lift.UniswapV2Pair.BurnPositionalFacts
import Blanc.Lift.UniswapV2Pair.TransferSourceCall

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first transfer request consumes the retained fourth original call,
including its physical entry bit and full reply. -/
theorem BurnFourCalls.transferSourceCall {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (staticContext : frame.context.isStatic = sevm.isStatic)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.transfer frame.context.pair 3 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnTransfer0 current.state.token0
          (.transfer (Sevm.dataWord sevm 4).toAdr (r.three.amount0 r.pricing)))
        { success := true, returndata := r.transfer.returned.devm.returnData,
          codeExists := r.transfer.occurrence.slot.isSome, recoveryOutput := 0 } 3,
      observed.call = r.transfer ∧ observed.paths = paths := by
  let request := requestFor .burnTransfer0 current.state.token0
    (.transfer (Sevm.dataWord sevm 4).toAdr (r.three.amount0 r.pricing))
  obtain ⟨_, _, token, _, _⟩ := r.three.initial.cache_targets rep
  have word : burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff =
      current.state.token0.toB256 := by
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, token]
  have operands : (r.gas.toB256 :: current.state.token0.toB256 :: 0 :: 292 :: 68 ::
      292 :: 0 :: []) <<+ r.transfer.occurrence.node.devm.stack := by
    rw [r.transfer_input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.transfer.occurrence.node.devm.memory.read 292 68).1 = request.calldata := by
    rw [r.calldata]
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      B256.and_comm, and_mask_word, toAdr_toB256]
    rfl
  have flag : [1] <<+ r.transfer.returned.devm.stack := by
    rw [(r.actualReply success fork).1]
    exact pref_append _ _
  exact transfer_source_call_at (request := request) r.transfer rfl rfl
    (by intro digest v rr ss impossible; cases impossible)
    (by rw [r.transfer_sevm]; exact staticContext)
    (by rw [r.transfer_sevm]; exact pair) operands data flag rfl rfl rfl
    (by rw [r.transfer_sevm]; exact fork) queue

/-- The second transfer source request uses the actual first reply's moving
allocation and the retained fifth call's own slot and full reply. -/
theorem BurnFiveCalls.secondTransferSourceCall {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnFiveCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (staticContext : frame.context.isStatic = sevm.isStatic)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.second frame.context.pair 4 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnTransfer1 current.state.token1
          (.transfer (Sevm.dataWord sevm 4).toAdr (r.four.three.amount1 r.four.pricing)))
        { success := true, returndata := r.second.returned.devm.returnData,
          codeExists := r.second.occurrence.slot.isSome, recoveryOutput := 0 } 4,
      observed.call = r.second ∧ observed.paths = paths := by
  let request := requestFor .burnTransfer1 current.state.token1
    (.transfer (Sevm.dataWord sevm 4).toAdr (r.four.three.amount1 r.four.pricing))
  obtain ⟨_, _, _, token, _⟩ := r.four.three.initial.cache_targets rep
  have word : burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff =
      current.state.token1.toB256 := by
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, token]
  have operands : (r.gas.toB256 :: current.state.token1.toB256 :: 0 ::
      (r.four.replyPointer + 164) :: 68 :: (r.four.replyPointer + 164) :: 0 :: []) <<+
      r.second.occurrence.node.devm.stack := by
    rw [r.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.second.occurrence.node.devm.memory.read (r.four.replyPointer + 164).toNat 68).1 =
      request.calldata := by
    rw [r.calldata]
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      B256.and_comm, and_mask_word, toAdr_toB256]
    rfl
  have flag : [1] <<+ r.second.returned.devm.stack := by
    rw [(r.actualReply success fork).1]
    exact pref_append _ _
  exact transfer_source_call_at (request := request) r.second rfl rfl
    (by intro digest v rr ss impossible; cases impossible)
    (by rw [r.sevm_eq]; exact staticContext)
    (by rw [r.sevm_eq]; exact pair) operands data flag rfl rfl rfl
    (by rw [r.sevm_eq]; exact fork) queue

end Blanc.Lift.UniswapV2Pair
