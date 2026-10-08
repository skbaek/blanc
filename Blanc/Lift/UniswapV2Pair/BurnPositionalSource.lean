import Blanc.Lift.UniswapV2Pair.BurnPositionalFacts
import Blanc.Lift.UniswapV2Pair.StaticSourceCall
import Blanc.Lift.UniswapV2Pair.TransferSourceCall
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueExistence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first source balance request consumes this retained original slot. -/
theorem BurnInitialPair.firstSourceCall {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnInitialPair root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.first frame.context.pair 0 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnInitialBalance0 current.state.token0 (.balanceOf frame.context.pair))
        (feeObservedResult r.out0) 0,
      observed.call = r.first ∧ observed.paths = paths := by
  let request := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf frame.context.pair)
  have env : r.first.occurrence.node.sevm = sevm :=
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.first.sameFrame).trans
      ((Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.second.sameFrame).symm.trans r.second_sevm)
  obtain ⟨_, _, target, _, _⟩ := r.cache_targets rep
  have masked : (burnInitialToken0 sevm b).toAdr.toB256 = burnInitialToken0 sevm b := by
    rw [burnInitialToken0,
      show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      B256.and_comm, and_mask_word, toAdr_toB256]
  have word : burnInitialToken0 sevm b = current.state.token0.toB256 :=
    masked.symm.trans (congrArg Adr.toB256 target)
  have operands : (r.gas0.toB256 :: current.state.token0.toB256 :: 128 :: 36 ::
      128 :: 32 :: []) <<+ r.first.occurrence.node.devm.stack := by
    rw [r.first_input]
    change _ <<+ (r.gas0.toB256 :: burnInitialToken0 sevm b :: 128 :: 36 ::
      128 :: 32 :: _)
    rw [word]
    exact pref_append _ _
  have data : (r.first.occurrence.node.devm.memory.read 128 36).1 = request.calldata := by
    rw [r.first_input]
    rw [show request.calldata = ExternalOperation.encode (.balanceOf sevm.currentTarget) by
      simp only [request, requestFor, pair]]
    exact balanceRequestMemory_read getterInitMemory_ptr.wf sevm.currentTarget
  have flag : [1] <<+ r.first.returned.devm.stack := by
    rw [r.first_reply.stack]
    exact pref_append _ _
  have guard : (r.first.occurrence.node.devm.getCode current.state.token0).size.toB256 ≠ 0 := by
    rw [r.first_input]
    simp only [burnFirstCallInput, St, Devm.getCode_setMach]
    rw [← target]
    simpa only [burnInitialWorld0, burnInitialToken0] using r.first_guard
  exact static_source_call_at (request := request) r.first rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [env]; exact pair) operands data flag rfl r.first_reply.returnData.symm rfl
    guard (by rw [env]; exact fork) queue

/-- The second source balance request consumes the first actual return's successor slot. -/
theorem BurnInitialPair.secondSourceCall {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnInitialPair root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.second frame.context.pair 1 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnInitialBalance1 current.state.token1 (.balanceOf frame.context.pair))
        (feeObservedResult r.out1) 1,
      observed.call = r.second ∧ observed.paths = paths := by
  let request := requestFor .burnInitialBalance1 current.state.token1 (.balanceOf frame.context.pair)
  obtain ⟨_, _, _, token, _⟩ := r.cache_targets rep
  have target : (burnInitialTarget1 sevm b).toAdr = current.state.token1 := by
    rw [burnInitialTarget1,
      show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, toAdr_toB256]
    exact token
  have word : burnInitialTarget1 sevm b = current.state.token1.toB256 := by
    rw [burnInitialTarget1,
      show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, token]
  have operands : (r.gas1.toB256 :: current.state.token1.toB256 :: 128 :: 36 ::
      128 :: 32 :: []) <<+ r.second.occurrence.node.devm.stack := by
    rw [r.second_input]
    simp only [burnInitialSecondInput, St.stack, word]
    exact pref_append _ _
  have data : (r.second.occurrence.node.devm.memory.read 128 36).1 = request.calldata := by
    rw [r.second_input]
    rw [show request.calldata = ExternalOperation.encode (.balanceOf sevm.currentTarget) by
      simp only [request, requestFor, pair]]
    exact balanceRequestMemory_read
      (balanceReplyMemory_ptr r.out0 (balanceRequestMemory_ptr getterInitMemory_ptr _)).wf _
  have flag : [1] <<+ r.second.returned.devm.stack := by
    rw [r.second_reply.stack]
    exact pref_append _ _
  have guard : (r.second.occurrence.node.devm.getCode current.state.token1).size.toB256 ≠ 0 := by
    rw [r.second_input]
    simp only [burnInitialSecondInput, St, Devm.getCode_setMach]
    rw [← target]
    simpa only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state]
      using r.second_guard
  exact static_source_call_at (request := request) r.second rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.second_sevm]; exact pair) operands data flag rfl r.second_reply.returnData.symm rfl
    guard (by rw [r.second_sevm]; exact fork) queue

end Blanc.Lift.UniswapV2Pair
