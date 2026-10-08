import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.ExecutionPathLocator

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Every supplied original call has its exact settlement-filtered frame queue.
No code-existence, child commitment or successful-child premise is needed. -/
theorem CallOccurrenceStep.sourceSlotQueue {root : Exec.Deriv} {x : Xinst}
    (call : CallOccurrenceStep root x) (pair : Adr) (index : Nat) :
    ∃ paths, SourceSlotQueue call pair index paths := by
  have actual : Step.Run
      (Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
        call.occurrence.node.devm⟩)
      call.occurrence.slot (.ok call.returned.devm) := by
    rw [Evm.step_next call.occurrence.decoded]
    change Ninst.StepRun call.occurrence.node.pc call.occurrence.node.sevm
      call.occurrence.node.devm call.occurrence.instruction
      call.occurrence.slot (.ok call.returned.devm)
    rw [← call.result]
    exact call.occurrence.stepRun
  cases slotEq : call.occurrence.slot with
  | none => exact ⟨[], Or.inl ⟨slotEq, rfl⟩⟩
  | some pairSlot =>
    rcases pairSlot with ⟨childEvm, raw⟩
    have actualSome : Step.Run
        (Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
          call.occurrence.node.devm⟩)
        (.some ⟨childEvm, raw⟩) (.ok call.returned.devm) := by
      simpa only [slotEq] using actual
    obtain ⟨callee, resume, pc', spawn, enter, resumed⟩ := Step.Run.some_inv actualSome
    have filled := call.occurrence.filled
    rw [slotEq] at filled
    obtain ⟨childRun⟩ := filled
    obtain ⟨next, exactRun⟩ := Exec.exists_next_of_run_spawn call.occurrence.node.exc
      spawn enter childRun resumed.symm
    refine ⟨_, Or.inr ⟨childEvm, raw, callee, resume, pc', childRun, next,
      spawn, enter, resumed.symm, slotEq, exactRun, rfl⟩⟩

end Blanc.Lift.UniswapV2Pair
