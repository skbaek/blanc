import Blanc.Lift.UniswapV2Pair.MintPositionalFacts
import Blanc.Lift.UniswapV2Pair.StaticSourceCall

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first typed balance request names this certificate's original call. -/
theorem MintRootCallPositions.firstSourceCall {root : Exec.Deriv} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {paths : List Exec.LocatedFrame}
    (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (fork : CoveredFork root.sevm.benvStat.fork)
    (queue : SourceSlotQueue r.first.call root.sevm.currentTarget 0 paths) :
    let ctx := writerContext root.sevm invocation
    ∃ observed : SourceCallAt root (mintSourceLockedFrame current ctx (Sevm.dataWord root.sevm 4).toAdr)
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair))
        (feeObservedResult r.out0) 0,
      observed.call = r.first.call ∧ observed.paths = paths := by
  dsimp only
  let ctx := writerContext root.sevm invocation
  let request := requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)
  obtain ⟨_, _, target, _, _⟩ := r.cache_targets rep
  have word : mintRootToken0 root b = current.state.token0.toB256 := by
    have same := congrArg Adr.toB256 target
    simpa only [mintRootToken0, toAdr_toB256] using same
  have operands : (r.first.gas.toB256 :: current.state.token0.toB256 :: 128 :: 36 ::
      128 :: 32 :: []) <<+ r.first.call.occurrence.node.devm.stack := by
    rw [r.first.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.first.call.occurrence.node.devm.memory.read 128 36).1 = request.calldata := by
    rw [r.first.input]
    exact balanceRequestMemory_read getterInitMemory_ptr.wf root.sevm.currentTarget
  have flag : [1] <<+ r.first.call.returned.devm.stack := by
    rw [r.post0.stack]
    exact pref_append _ _
  have guard : (r.first.call.occurrence.node.devm.getCode current.state.token0).size.toB256 ≠ 0 := by
    rw [r.first.input]
    simp only [St, Devm.getCode_setMach]
    simpa only [target] using r.guarded0
  exact static_source_call_at (request := request) r.first.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.first.sevm_eq]; rfl) operands data flag rfl r.post0.returnData.symm rfl
    guard (by rw [r.first.sevm_eq]; exact fork) queue

/-- The second request uses the first call's actual returned parent and reply. -/
theorem MintRootCallPositions.secondSourceCall {root : Exec.Deriv} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {paths : List Exec.LocatedFrame}
    (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (fork : CoveredFork root.sevm.benvStat.fork)
    (queue : SourceSlotQueue r.second.call root.sevm.currentTarget 1 paths) :
    let ctx := writerContext root.sevm invocation
    ∃ observed : SourceCallAt root
        ((mintSourceLockedFrame current ctx (Sevm.dataWord root.sevm 4).toAdr).beginResume
          (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)))
        (requestFor .mintBalance1 current.state.token1 (.balanceOf ctx.pair))
        (feeObservedResult r.out1) 1,
      observed.call = r.second.call ∧ observed.paths = paths := by
  dsimp only
  let ctx := writerContext root.sevm invocation
  let request := requestFor .mintBalance1 current.state.token1 (.balanceOf ctx.pair)
  obtain ⟨_, _, _, target, _⟩ := r.cache_targets rep
  have word : mintRootToken1 r.first = current.state.token1.toB256 := by
    have same := congrArg Adr.toB256 target
    simpa only [mintRootToken1, toAdr_toB256] using same
  have env := r.first.returned_sevm
  have operands : (r.second.gas.toB256 :: current.state.token1.toB256 :: 128 :: 36 ::
      128 :: 32 :: []) <<+ r.second.call.occurrence.node.devm.stack := by
    rw [r.second.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.second.call.occurrence.node.devm.memory.read 128 36).1 = request.calldata := by
    rw [r.second.input]
    simp only [St.memory, env]
    exact balanceRequestMemory_read
      (balanceReplyMemory_ptr r.out0 (balanceRequestMemory_ptr getterInitMemory_ptr _)).wf _
  have flag : [1] <<+ r.second.call.returned.devm.stack := by
    rw [r.post1.stack]
    exact pref_append _ _
  have guard : (r.second.call.occurrence.node.devm.getCode current.state.token1).size.toB256 ≠ 0 := by
    rw [r.second.input]
    simp only [St, Devm.getCode_setMach]
    simpa only [target] using r.guarded1
  exact static_source_call_at (request := request) r.second.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.second.sevm_eq, env]; rfl) operands data flag rfl r.post1.returnData.symm rfl
    guard (by rw [r.second.sevm_eq, env]; exact fork) queue

/-- The factory source request uses the same third occurrence that supplies the
physical fee word to the original pricing and public suffixes. -/
theorem MintRootCallPositions.feeSourceCall {root : Exec.Deriv} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {paths : List Exec.LocatedFrame}
    (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (fork : CoveredFork root.sevm.benvStat.fork)
    (queue : SourceSlotQueue r.fee.occurrence.call root.sevm.currentTarget 2 paths) :
    let ctx := writerContext root.sevm invocation
    ∃ observed : SourceCallAt root
        (mintSourceFeeFrame current ctx (Sevm.dataWord root.sevm 4).toAdr)
        (requestFor .mintFeeTo current.state.factory .feeTo)
        (feeObservedResult r.fee.out) 2,
      observed.call = r.fee.occurrence.call ∧ observed.paths = paths := by
  dsimp only
  let request := requestFor .mintFeeTo current.state.factory .feeTo
  obtain ⟨_, _, _, _, target⟩ := r.cache_targets rep
  have env1 := r.second.returned_sevm.trans r.first.returned_sevm
  have word : feeFactoryWord r.second.call.returned.sevm r.second.call.returned.devm =
      current.state.factory.toB256 := by
    have same := congrArg Adr.toB256 target
    simpa only [env1, feeFactoryWord, toAdr_toB256] using same
  have operands : (r.fee.occurrence.gas.toB256 :: current.state.factory.toB256 :: 128 :: 4 ::
      128 :: 32 :: []) <<+ r.fee.occurrence.call.occurrence.node.devm.stack := by
    rw [r.fee.occurrence.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have mem0 := balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget
  have mem1 := balanceReplyMemory_ptr r.out0 mem0
  have mem2 := balanceRequestMemory_ptr mem1 r.first.call.returned.sevm.currentTarget
  have mem3 := balanceReplyMemory_ptr r.out1 mem2
  have data : (r.fee.occurrence.call.occurrence.node.devm.memory.read 128 4).1 = request.calldata := by
    rw [r.fee.occurrence.input]
    exact feeRequestMemory_read mem3.wf
  have flag : [1] <<+ r.fee.occurrence.call.returned.devm.stack := by
    rw [r.fee.reply.stack]
    exact pref_append _ _
  have guard : (r.fee.occurrence.call.occurrence.node.devm.getCode current.state.factory).size.toB256 ≠ 0 := by
    rw [r.fee.occurrence.input]
    simp only [St, Devm.getCode_setMach]
    have actual := r.fee.occurrence.code_exists
    simpa only [env1, target] using actual
  exact static_source_call_at (request := request) r.fee.occurrence.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.fee.occurrence.sevm_eq, env1]; rfl) operands data flag rfl r.fee.reply.returnData.symm rfl
    guard (by rw [r.fee.occurrence.sevm_eq, env1]; exact fork) queue

end Blanc.Lift.UniswapV2Pair
