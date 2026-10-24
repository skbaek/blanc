import Blanc.Lift.UniswapV2Pair.MintPositionalFacts
import Blanc.Lift.UniswapV2Pair.StaticSourceCall
import Blanc.Lift.UniswapV2Pair.PairFeeSourceCall

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem MintRootCallPositionsH.firstSourceCall {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {paths : List Exec.LocatedFrame}
    (r : MintRootCallPositionsH root b W1 A2 F)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (stateGas : root.sevm.benvStat.rules.stateGas = none)
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
  exact static_source_call_atH (request := request) r.first.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.first.sevm_eq]; rfl) operands data flag rfl r.post0.returnData.symm rfl
    guard (by rw [r.first.sevm_eq]; exact stateGas) queue


theorem MintRootCallPositionsH.secondSourceCall {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {paths : List Exec.LocatedFrame}
    (r : MintRootCallPositionsH root b W1 A2 F)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (stateGas : root.sevm.benvStat.rules.stateGas = none)
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
  have word : mintToken1Of r.first.call.returned = current.state.token1.toB256 := by
    have same := congrArg Adr.toB256 target
    simpa only [mintToken1Of, toAdr_toB256] using same
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
  exact static_source_call_atH (request := request) r.second.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.second.sevm_eq, env]; rfl) operands data flag rfl r.post1.returnData.symm rfl
    guard (by rw [r.second.sevm_eq, env]; exact stateGas) queue


theorem MintRootCallPositionsH.feeSourceCall {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {paths : List Exec.LocatedFrame}
    (r : MintRootCallPositionsH root b W1 A2 F)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (queue : SourceSlotQueue r.fee.occurrence.call root.sevm.currentTarget 2 paths) :
    let ctx := writerContext root.sevm invocation
    ∃ observed : SourceCallAt root
        (mintSourceFeeFrame current ctx (Sevm.dataWord root.sevm 4).toAdr)
        (requestFor .mintFeeTo current.state.factory .feeTo)
        (feeObservedResult r.fee.out) 2,
      observed.call = r.fee.occurrence.call ∧ observed.paths = paths := by
  dsimp only
  obtain ⟨_, _, _, _, target⟩ := r.cache_targets rep
  have env1 := r.second.returned_sevm.trans r.first.returned_sevm
  have word : feeFactoryWord r.second.call.returned.sevm r.second.call.returned.devm =
      current.state.factory.toB256 := by
    have same := congrArg Adr.toB256 target
    simpa only [env1, feeFactoryWord, toAdr_toB256] using same
  have mem0 := balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget
  have mem1 := balanceReplyMemory_ptr r.out0 mem0
  have mem2 := balanceRequestMemory_ptr mem1 r.first.call.returned.sevm.currentTarget
  have mem3 := balanceReplyMemory_ptr r.out1 mem2
  exact r.fee.sourceCall .mintFeeTo 2 word (by rw [env1]; rfl) mem3.wf
    (by rw [env1]; exact stateGas) queue


end Blanc.Lift.UniswapV2Pair
