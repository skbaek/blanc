import Blanc.Lift.UniswapV2Pair.BurnPositionalFacts
import Blanc.Lift.UniswapV2Pair.StaticSourceCall
import Blanc.Lift.UniswapV2Pair.PairFeeSourceCall
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

/-- The factory source request consumes this same third call and its own reply. -/
theorem BurnThreeCalls.feeSourceCall {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnThreeCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.fee.occurrence.call frame.context.pair 2 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnFeeTo current.state.factory .feeTo) (feeObservedResult r.fee.out) 2,
      observed.call = r.fee.occurrence.call ∧ observed.paths = paths := by
  have env : r.initial.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.initial.second.edge).trans r.initial.second_sevm
  obtain ⟨_, _, _, _, target⟩ := r.initial.cache_targets rep
  have word : feeFactoryWord r.initial.second.returned.sevm
      (feeBurnWorld r.initial.second.returned.sevm r.initial.second.returned.devm) =
      current.state.factory.toB256 := by
    rw [env]
    simpa only [feeFactoryWord, toAdr_toB256] using congrArg Adr.toB256 target
  have mem := balanceReplyMemory_ptr r.initial.out1
    (balanceRequestMemory_ptr
      (balanceReplyMemory_ptr r.initial.out0
        (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)) sevm.currentTarget)
  have scratch := feeBurnMemory_ptr mem sevm.currentTarget
  exact r.fee.sourceCall .burnFeeTo 2 word (by rw [env]; exact pair)
    (by rw [env]; exact scratch.wf) (by rw [env]; exact fork) queue

/-- The first final balance source request names the retained sixth original slot. -/
theorem BurnSevenCalls.final0SourceCall {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnSevenCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.final0.call frame.context.pair 5 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnFinalBalance0 current.state.token0 (.balanceOf frame.context.pair))
        (feeObservedResult r.final0.out) 5,
      observed.call = r.final0.call ∧ observed.paths = paths := by
  let request := requestFor .burnFinalBalance0 current.state.token0 (.balanceOf frame.context.pair)
  have env : r.five.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.five.second.edge).trans r.five.sevm_eq
  obtain ⟨_, _, token, _, _⟩ := r.five.four.three.initial.cache_targets rep
  have target : (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
      current.state.token0 := by
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, toAdr_toB256]
    exact token
  have word : burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff =
      current.state.token0.toB256 := by
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, token]
  have operands : (r.final0.gas.toB256 :: current.state.token0.toB256 :: r.five.finalPointer :: 36 ::
      r.five.finalPointer :: 32 :: []) <<+ r.final0.call.occurrence.node.devm.stack := by
    rw [r.final0.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.final0.call.occurrence.node.devm.memory.read r.five.finalPointer.toNat 36).1 =
      request.calldata := by
    rw [r.final0.input]
    simpa only [St.memory, env, request, requestFor, pair] using r.final0.calldata
  have flag : [1] <<+ r.final0.call.returned.devm.stack := by
    rw [r.final0.reply.stack]
    exact pref_append _ _
  have guard : (r.final0.call.occurrence.node.devm.getCode current.state.token0).size.toB256 ≠ 0 := by
    rw [r.final0.input]
    simp only [St, Devm.getCode_setMach]
    rw [← target]
    exact r.final0.code_exists
  exact static_source_call_at (request := request) r.final0.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.final0.sevm_eq, env]; exact pair) operands data flag rfl r.final0.reply.returnData.symm rfl
    guard (by rw [r.final0.sevm_eq, env]; exact fork) queue

/-- The second final balance source request names the retained seventh original slot. -/
theorem BurnSevenCalls.final1SourceCall {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    {paths : List Exec.LocatedFrame} (r : BurnSevenCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (pair : frame.context.pair = sevm.currentTarget)
    (fork : CoveredFork sevm.benvStat.fork)
    (queue : SourceSlotQueue r.final1.call frame.context.pair 6 paths) :
    ∃ observed : SourceCallAt root frame
        (requestFor .burnFinalBalance1 current.state.token1 (.balanceOf frame.context.pair))
        (feeObservedResult r.final1.out) 6,
      observed.call = r.final1.call ∧ observed.paths = paths := by
  let request := requestFor .burnFinalBalance1 current.state.token1 (.balanceOf frame.context.pair)
  have env5 : r.five.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.five.second.edge).trans r.five.sevm_eq
  have env : r.final0.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.final0.call.edge).trans (r.final0.sevm_eq.trans env5)
  obtain ⟨_, _, _, token, _⟩ := r.five.four.three.initial.cache_targets rep
  have target : (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
      current.state.token1 := by
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, toAdr_toB256]
    exact token
  have word : burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff =
      current.state.token1.toB256 := by
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      and_mask_word, token]
  have operands : (r.final1.gas.toB256 :: current.state.token1.toB256 :: r.five.finalPointer :: 36 ::
      r.five.finalPointer :: 32 :: []) <<+ r.final1.call.occurrence.node.devm.stack := by
    rw [r.final1.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.final1.call.occurrence.node.devm.memory.read r.five.finalPointer.toNat 36).1 =
      request.calldata := by
    rw [r.final1.input]
    simpa only [St.memory, env, request, requestFor, pair] using r.final1.calldata
  have flag : [1] <<+ r.final1.call.returned.devm.stack := by
    rw [r.final1.reply.stack]
    exact pref_append _ _
  have guard : (r.final1.call.occurrence.node.devm.getCode current.state.token1).size.toB256 ≠ 0 := by
    rw [r.final1.input]
    simp only [St, Devm.getCode_setMach]
    rw [← target]
    exact r.final1.code_exists
  exact static_source_call_at (request := request) r.final1.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.final1.sevm_eq, env]; exact pair) operands data flag rfl r.final1.reply.returnData.symm rfl
    guard (by rw [r.final1.sevm_eq, env]; exact fork) queue

end Blanc.Lift.UniswapV2Pair
