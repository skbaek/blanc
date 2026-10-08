import Blanc.Lift.UniswapV2Pair.PairFeeObservation
import Blanc.Lift.UniswapV2Pair.FeeMintSource
import Blanc.Lift.UniswapV2Pair.StaticSourceCall

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The fee source request names this same original factory slot and full reply. -/
theorem PairFeeObservation.sourceCall {root start : Exec.Deriv} {b : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc}
    {frame : Frame} {target : Adr} {paths : List Exec.LocatedFrame}
    (r : PairFeeObservation root start b M r1 r0 ρ R K) (site : CallSite) (index : Nat)
    (word : feeFactoryWord start.sevm b = target.toB256)
    (pair : frame.context.pair = start.sevm.currentTarget)
    (memory : Mem.Wf M) (fork : CoveredFork start.sevm.benvStat.fork)
    (queue : SourceSlotQueue r.occurrence.call frame.context.pair index paths) :
    ∃ observed : SourceCallAt root frame (requestFor site target .feeTo)
        (feeObservedResult r.out) index,
      observed.call = r.occurrence.call ∧ observed.paths = paths := by
  let request := requestFor site target .feeTo
  have operands : (r.occurrence.gas.toB256 :: target.toB256 :: 128 :: 4 ::
      128 :: 32 :: []) <<+ r.occurrence.call.occurrence.node.devm.stack := by
    rw [r.occurrence.input]
    simp only [St.stack, word]
    exact pref_append _ _
  have data : (r.occurrence.call.occurrence.node.devm.memory.read 128 4).1 = request.calldata := by
    rw [r.occurrence.input]
    exact feeRequestMemory_read memory
  have flag : [1] <<+ r.occurrence.call.returned.devm.stack := by
    rw [r.reply.stack]
    exact pref_append _ _
  have guard : (r.occurrence.call.occurrence.node.devm.getCode target).size.toB256 ≠ 0 := by
    rw [r.occurrence.input]
    simp only [St, Devm.getCode_setMach]
    simpa only [word, toAdr_toB256] using r.occurrence.code_exists
  exact static_source_call_at (request := request) r.occurrence.call rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.occurrence.sevm_eq]; exact pair) operands data flag rfl r.reply.returnData.symm rfl
    guard (by rw [r.occurrence.sevm_eq]; exact fork) queue

end Blanc.Lift.UniswapV2Pair
